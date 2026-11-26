//! The account behind a profile: `cargo run -p binance-example --bin account -- <profile>`.
//!
//! Prints whether it can trade, its commission rates, its non-zero balances, its open orders and
//! Binance's clock against ours. The first two requests are signed: they fail on a wrong key or
//! passphrase, and on a clock that is too far off.

use std::path::Path;
use std::process::ExitCode;

use binance_example::clocks;
use binance_example::profile::Profile;
use binance_sdk::spot::rest_api::{GetAccountParams, GetOpenOrdersParams};

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
    let name = std::env::args().nth(1).ok_or("usage: account <profile>")?;
    let profile = Profile::load(Path::new(PROFILES), &name)?;
    let client = profile.rest()?;
    println!("{name} ({:?})", profile.env);

    let params = GetAccountParams::builder()
        .omit_zero_balances(true)
        .build()?;
    let account = client.get_account(params).await?.data().await?;
    println!(
        "account type {}, can trade {}, permissions {}",
        show(&account.account_type),
        show(&account.can_trade),
        account.permissions.unwrap_or_default().join(", ")
    );
    if let Some(rates) = account.commission_rates {
        println!(
            "commission: maker {}, taker {}, buyer {}, seller {}",
            show(&rates.maker),
            show(&rates.taker),
            show(&rates.buyer),
            show(&rates.seller)
        );
    }
    let mut balances = account.balances.unwrap_or_default();
    balances.sort_by(|a, b| a.asset.cmp(&b.asset));
    println!(
        "{} non-zero balances (asset, free, locked):",
        balances.len()
    );
    for b in &balances {
        println!(
            "  {:<12} {:>24} {:>24}",
            show(&b.asset),
            show(&b.free),
            show(&b.locked)
        );
    }

    let orders = client
        .get_open_orders(GetOpenOrdersParams::builder().build()?)
        .await?
        .data()
        .await?;
    println!("{} open orders:", orders.len());
    for o in &orders {
        println!(
            "  {} {} {} {} of {} done, price {}, {}, client id {}",
            show(&o.symbol),
            show(&o.side),
            show(&o.r#type),
            show(&o.executed_qty),
            show(&o.orig_qty),
            show(&o.price),
            show(&o.status),
            show(&o.client_order_id)
        );
    }

    let (server, ours) = clocks(&client).await?;
    println!(
        "server time {server} ms, ours {ours} ms, offset {} ms",
        server - ours
    );
    Ok(())
}

/// A field Binance may leave out, as `?` when it did.
fn show<T: ToString>(field: &Option<T>) -> String {
    field.as_ref().map_or_else(|| "?".to_string(), T::to_string)
}
