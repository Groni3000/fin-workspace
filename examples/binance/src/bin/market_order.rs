//! Places one market order and prints Binance's whole answer:
//! `cargo run -p binance-example --bin market_order -- <profile> <symbol> <buy|sell> <quantity>`.
//!
//! The quantity goes to Binance as typed, unrounded, so its own checks (step, minimum value,
//! balance) answer.

use std::path::Path;
use std::process::ExitCode;

use binance_example::instruments;
use binance_example::orders::{self, BoxError};
use binance_example::profile::Profile;
use binance_sdk::spot::rest_api::NewOrderSideEnum;
use rust_decimal::Decimal;

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
    let mut args = std::env::args().skip(1);
    let usage = "usage: market_order <profile> <symbol> <buy|sell> <quantity>";
    let name = args.next().ok_or(usage)?;
    let symbol = args.next().ok_or(usage)?.to_uppercase();
    let side = match args.next().ok_or(usage)?.to_lowercase().as_str() {
        "buy" => NewOrderSideEnum::Buy,
        "sell" => NewOrderSideEnum::Sell,
        other => return Err(format!("side must be buy or sell, not {other:?}").into()),
    };
    let quantity: Decimal = args.next().ok_or(usage)?.parse()?;
    if instruments::by_symbol(&symbol).is_none() {
        let listed: Vec<_> = instruments::all().iter().map(|l| l.symbol).collect();
        return Err(format!("{symbol} is not listed; listed: {}", listed.join(", ")).into());
    }
    let profile = Profile::load(Path::new(PROFILES), &name)?;
    let client = orders::trading_client(&profile)?;

    println!(
        "{name} ({:?}): market {side:?} {quantity} {symbol}",
        profile.env
    );
    let (response, took) = orders::place_market(&client, &symbol, side, quantity).await?;
    println!(
        "answered in {} ms:\n{}",
        took.as_millis(),
        serde_json::to_string_pretty(&response)?
    );
    Ok(())
}
