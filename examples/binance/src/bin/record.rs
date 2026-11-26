//! Records a 1-second kline stream:
//! `cargo run -p binance-example --bin record -- <profile> <symbol> [seconds]`.
//!
//! Writes every WebSocket event to `examples/binance/recordings/`, one line each:
//! `<receive time, ns since the Unix epoch>\t<kind>\t<payload>`. Kinds: `message` (the raw JSON),
//! `close`, `error`, `ping`, `pong`, `open`, and `failed` for our own failures. Without
//! `seconds`, runs until Ctrl-C.

use std::fs::File;
use std::io::{LineWriter, Write};
use std::path::Path;
use std::process::ExitCode;
use std::sync::mpsc::{RecvTimeoutError, Sender};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use binance_example::bridge;
use binance_example::profile::Profile;
use binance_sdk::config::ConfigurationWebsocketStreams;
use binance_sdk::models::WebsocketEvent;
use binance_sdk::spot::websocket_streams::{KlineIntervalEnum, KlineParams};
use tokio::sync::mpsc::UnboundedReceiver;

const PROFILES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/profiles.toml");
const RECORDINGS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/recordings");

/// One line of the recording.
struct Line {
    received_ns: i128,
    kind: &'static str,
    payload: String,
}

impl Line {
    fn now(kind: &'static str, payload: String) -> Self {
        let received_ns = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos() as i128);
        Self {
            received_ns,
            kind,
            payload,
        }
    }

    fn of(event: WebsocketEvent) -> Self {
        match event {
            WebsocketEvent::Message(raw) => Self::now("message", raw),
            WebsocketEvent::Open => Self::now("open", String::new()),
            WebsocketEvent::Close(code, reason) => Self::now("close", format!("{code} {reason}")),
            WebsocketEvent::Error(e) => Self::now("error", e),
            WebsocketEvent::Ping => Self::now("ping", String::new()),
            WebsocketEvent::Pong => Self::now("pong", String::new()),
        }
    }
}

fn main() -> ExitCode {
    binance_sdk::logger::init();
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut args = std::env::args().skip(1);
    let usage = "usage: record <profile> <symbol> [seconds]";
    let name = args.next().ok_or(usage)?;
    let symbol = args.next().ok_or(usage)?.to_uppercase();
    let seconds: Option<u64> = args.next().map(|s| s.parse()).transpose()?;
    let env = Profile::load(Path::new(PROFILES), &name)?.env;

    std::fs::create_dir_all(RECORDINGS)?;
    let started = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();
    let path = Path::new(RECORDINGS).join(format!("{name}-{symbol}-kline_1s-{started}.tsv"));
    let mut out = LineWriter::new(File::create(&path)?);
    println!(
        "recording {symbol} on {name} ({env:?}) to {}",
        path.display()
    );

    let stream = symbol.to_lowercase();
    let bridge = bridge::spawn(
        move |lines: Sender<Line>, mut stop: UnboundedReceiver<()>| async move {
            let failed = |e: String| {
                let _ = lines.send(Line::now("failed", e));
            };
            let config = match ConfigurationWebsocketStreams::builder().build() {
                Ok(config) => config,
                Err(e) => return failed(e.to_string()),
            };
            let connection = match env.streams(config).connect().await {
                Ok(connection) => connection,
                Err(e) => return failed(format!("connect: {e}")),
            };
            let events = lines.clone();
            let _subscription = connection.subscribe_on_ws_events(move |event| {
                let _ = events.send(Line::of(event));
            });
            let params = match KlineParams::builder(stream, KlineIntervalEnum::Interval1s).build() {
                Ok(params) => params,
                Err(e) => return failed(e.to_string()),
            };
            if let Err(e) = connection.kline(params).await {
                return failed(format!("subscribe: {e}"));
            }
            let _ = stop.recv().await;
            if let Err(e) = connection.disconnect().await {
                failed(format!("disconnect: {e}"));
            }
        },
    )?;

    let deadline = seconds.map(|s| Instant::now() + Duration::from_secs(s));
    let mut written = 0_u64;
    let mut write = |line: Line, out: &mut LineWriter<File>| -> std::io::Result<()> {
        written += 1;
        writeln!(out, "{}\t{}\t{}", line.received_ns, line.kind, line.payload)
    };
    loop {
        let next = match deadline {
            Some(deadline) => {
                bridge.recv_timeout(deadline.saturating_duration_since(Instant::now()))
            }
            None => bridge.recv().map_err(|_| RecvTimeoutError::Disconnected),
        };
        match next {
            Ok(line) => write(line, &mut out)?,
            Err(RecvTimeoutError::Timeout) => break,
            Err(RecvTimeoutError::Disconnected) => {
                eprintln!("the stream task ended early");
                break;
            }
        }
    }
    // Stop: the task disconnects and ends; the events it sent until then are still written.
    let _ = bridge.send(());
    while let Ok(line) = bridge.recv() {
        write(line, &mut out)?;
    }
    bridge.finish().map_err(|_| "the bridge thread panicked")?;
    println!("{written} lines in {}", path.display());
    Ok(())
}
