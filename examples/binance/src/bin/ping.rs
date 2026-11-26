//! Connectivity check: `cargo run -p binance-example --bin ping -- <profile>`.
//!
//! Loads the profile from `examples/binance/profiles.toml`, pings its environment and prints its
//! clock against ours. Signed requests carry our timestamp, so a large offset will get them
//! rejected. The ping itself is unsigned.

use std::path::Path;
use std::process::ExitCode;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

use binance_example::profile::Profile;

const PROFILES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/profiles.toml");

#[tokio::main]
async fn main() -> ExitCode {
    match run().await {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

async fn run() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let name = std::env::args().nth(1).ok_or("usage: ping <profile>")?;
    let profile = Profile::load(Path::new(PROFILES), &name)?;
    let client = profile.rest()?;

    let started = Instant::now();
    client.ping().await?.data().await?;
    println!(
        "{name} ({:?}): ping {} ms",
        profile.env,
        started.elapsed().as_millis()
    );

    let sent = SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis() as i64;
    let server = client
        .time()
        .await?
        .data()
        .await?
        .server_time
        .ok_or("no serverTime")?;
    let received = SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis() as i64;
    let ours = (sent + received) / 2;
    println!(
        "server time {server} ms, ours {ours} ms, offset {} ms",
        server - ours
    );
    Ok(())
}
