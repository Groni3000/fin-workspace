//! The bridge against a live environment: `cargo run -p binance-example --bin clock -- <profile>`.
//!
//! The bridge thread asks Binance for its time every second; the main thread prints each answer
//! with our clock's offset. Runs until Ctrl-C.

use std::path::Path;
use std::process::ExitCode;
use std::sync::mpsc::Sender;
use std::time::Duration;

use binance_example::profile::Profile;
use binance_example::{bridge, clocks};
use tokio::sync::mpsc::UnboundedReceiver;

const PROFILES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/profiles.toml");

enum Tick {
    Clocks { server: i64, ours: i64 },
    Error(String),
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let name = std::env::args().nth(1).ok_or("usage: clock <profile>")?;
    let profile = Profile::load(Path::new(PROFILES), &name)?;
    let client = profile.rest()?;

    let bridge = bridge::spawn(
        move |ticks: Sender<Tick>, _: UnboundedReceiver<()>| async move {
            let mut every_second = tokio::time::interval(Duration::from_secs(1));
            loop {
                every_second.tick().await;
                let tick = match clocks(&client).await {
                    Ok((server, ours)) => Tick::Clocks { server, ours },
                    Err(e) => Tick::Error(e.to_string()),
                };
                if ticks.send(tick).is_err() {
                    return;
                }
            }
        },
    )?;

    while let Ok(tick) = bridge.recv() {
        match tick {
            Tick::Clocks { server, ours } => {
                println!(
                    "server {server} ms, ours {ours} ms, offset {} ms",
                    server - ours
                )
            }
            Tick::Error(e) => eprintln!("time request failed: {e}"),
        }
    }
    bridge.finish().map_err(|_| "the bridge thread panicked")?;
    Ok(())
}
