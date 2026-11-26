//! Buys `quantity` at market, then sells the same quantity, printing the account before, between
//! and after: `cargo run -p binance-example --bin round_trip -- <profile> <symbol> <quantity>`.
//!
//! With fees paid in BNB the buy brings exactly `quantity`, so the sell goes through and leaves
//! nothing behind. With fees taken from the bought asset the buy brings a little less, and the
//! sell fails unless the account already held the difference.

use std::path::Path;
use std::process::ExitCode;

use binance_example::instruments;
use binance_example::orders::{self, BoxError, show};
use binance_example::profile::Profile;
use binance_sdk::spot::rest_api::{NewOrderSideEnum, RestApi};
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
    let usage = "usage: round_trip <profile> <symbol> <quantity>";
    let name = args.next().ok_or(usage)?;
    let symbol = args.next().ok_or(usage)?.to_uppercase();
    let quantity: Decimal = args.next().ok_or(usage)?.parse()?;
    if instruments::by_symbol(&symbol).is_none() {
        let listed: Vec<_> = instruments::all().iter().map(|l| l.symbol).collect();
        return Err(format!("{symbol} is not listed; listed: {}", listed.join(", ")).into());
    }
    let profile = Profile::load(Path::new(PROFILES), &name)?;
    let client = orders::trading_client(&profile)?;

    println!("== {name} ({:?}), before", profile.env);
    orders::print_commission(&client, &symbol).await?;
    orders::print_account(&client).await?;
    for side in [NewOrderSideEnum::Buy, NewOrderSideEnum::Sell] {
        println!("\n== market {side:?} {quantity} {symbol}");
        trade(&client, &symbol, side.clone(), quantity).await?;
        println!("\n== after the {side:?}");
        orders::print_account(&client).await?;
    }
    Ok(())
}

/// Places the order, waits until it is filled and prints its fills.
async fn trade(
    client: &RestApi,
    symbol: &str,
    side: NewOrderSideEnum,
    quantity: Decimal,
) -> Result<(), BoxError> {
    let (placed, took) = orders::place_market(client, symbol, side, quantity).await?;
    println!(
        "answered in {} ms: {}, client id {}",
        took.as_millis(),
        show(&placed.status),
        show(&placed.client_order_id)
    );
    for f in placed.fills.iter().flatten() {
        println!(
            "  fill {} @ {}, fee {} {}",
            show(&f.qty),
            show(&f.price),
            show(&f.commission),
            show(&f.commission_asset)
        );
    }
    let client_id = placed
        .client_order_id
        .ok_or("no clientOrderId in the answer")?;
    let filled = orders::wait_filled(client, symbol, &client_id).await?;
    println!(
        "filled: {} for {} quote",
        show(&filled.executed_qty),
        show(&filled.cummulative_quote_qty)
    );
    Ok(())
}
