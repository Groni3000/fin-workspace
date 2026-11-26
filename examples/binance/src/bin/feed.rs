//! Prints the live 1-second candles of a symbol, with the feed's reconnects and gaps:
//! `cargo run -p binance-example --bin feed -- <profile> <symbol>`.
//!
//! Each line starts with the time it was received (UTC). Runs until Ctrl-C; exits with an error
//! once the feed gives up.

use std::path::Path;
use std::process::ExitCode;

use binance_example::feed::{self, FeedEvent, Watchdog};
use binance_example::profile::Profile;
use binance_example::{bridge, instruments};
use jiff::Timestamp;
use mdata::{Candle, HasTimestamp, HasVolume};
use tokio::sync::mpsc::UnboundedReceiver;

const PROFILES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/profiles.toml");

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
    let usage = "usage: feed <profile> <symbol>";
    let name = args.next().ok_or(usage)?;
    let symbol = args.next().ok_or(usage)?.to_uppercase();
    if instruments::by_symbol(&symbol).is_none() {
        let listed: Vec<_> = instruments::all().iter().map(|l| l.symbol).collect();
        return Err(format!("{symbol} is not listed; listed: {}", listed.join(", ")).into());
    }
    let env = Profile::load(Path::new(PROFILES), &name)?.env;
    let streams = feed::streams(env)?;
    println!("{symbol} on {name} ({env:?})");

    let bridge = bridge::spawn(move |events, _: UnboundedReceiver<()>| async move {
        let forever = std::future::pending();
        feed::run(&streams, &symbol, Watchdog::default(), &events, forever).await;
    })?;
    while let Ok(event) = bridge.recv() {
        let now = Timestamp::now().strftime("%H:%M:%S%.3f");
        match event {
            FeedEvent::Kline(k) => {
                let c = k.candle;
                println!(
                    "{now}  candle  {}  o {}  h {}  l {}  c {}  v {}",
                    c.timestamp().strftime("%H:%M:%S"),
                    c.open(),
                    c.high(),
                    c.low(),
                    c.close(),
                    c.volume()
                );
            }
            FeedEvent::Gap(gap) => {
                let missing = (gap.until.as_millisecond() - gap.from.as_millisecond()) / 1000;
                let last = Timestamp::from_millisecond(gap.until.as_millisecond() - 1000)?;
                println!(
                    "{now}  gap     {} … {} ({missing} candles)",
                    gap.from.strftime("%H:%M:%S"),
                    last.strftime("%H:%M:%S")
                );
            }
            FeedEvent::Invalid { raw, error } => println!("{now}  invalid {error}: {raw}"),
            FeedEvent::Reconnecting { reason, after } => {
                println!("{now}  reconnecting in {after:?}: {reason}");
            }
            FeedEvent::Lost { blind, reason } => {
                return Err(format!(
                    "no candle for {} s; the last attempt: {reason}",
                    blind.as_secs()
                )
                .into());
            }
        }
    }
    bridge.finish().map_err(|_| "the bridge thread panicked")?;
    Err("the feed ended without saying why".into())
}
