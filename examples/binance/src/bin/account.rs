//! The account behind a profile: `cargo run -p binance-example --bin account -- <profile>`.
//!
//! Prints whether it can trade, its commission rates, its non-zero balances, its open orders and
//! Binance's clock against ours. The first two requests are signed: they fail on a wrong key or
//! passphrase, and on a clock that is too far off.

use std::path::Path;
use std::process::ExitCode;

use binance_example::clocks;
use binance_example::orders::{self, BoxError};
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

async fn run() -> Result<(), BoxError> {
    let name = std::env::args().nth(1).ok_or("usage: account <profile>")?;
    let profile = Profile::load(Path::new(PROFILES), &name)?;
    let client = profile.rest()?;
    println!("{name} ({:?})", profile.env);
    orders::print_account(&client).await?;

    let (server, ours) = clocks(&client).await?;
    println!(
        "server time {server} ms, ours {ours} ms, offset {} ms",
        server - ours
    );
    Ok(())
}
