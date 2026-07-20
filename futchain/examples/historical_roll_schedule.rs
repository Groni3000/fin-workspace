//! Generate a historical roll schedule for backtesting.
//!
//! Given a date range, produce the sequence of (active_contract, roll_date)
//! pairs — one row per contract that was the front month at some point in the
//! window. This is the data shape a backtester wants: each row describes which
//! contract you should be holding until the next row's `roll_date`.
//!
//! Uses GC (Gold) with its FND rule: last business day of the previous month,
//! minus 1 BDay defensive offset.
//!
//! Run with: `cargo run --example historical_roll_schedule`

use chrono::NaiveDate;
use futchain::{
    EndOfTrading, FutChain, ListedTenors,
    eot::{DateOffset, LastNthBDayOfPrevMonth},
};
use instrid::prelude::{Asset, AssetClass, FuturesContract, Mic, Tenor};
use tradeprim::currency::Currency;

fn main() {
    // GC (Gold): the OI-heavy months only.
    let listing = ListedTenors::new(vec![
        Tenor::February,
        Tenor::April,
        Tenor::June,
        Tenor::August,
        Tenor::December,
    ])
    .unwrap();

    // FND = last BDay of prev month, then -1 BDay defensive.
    let rule = LastNthBDayOfPrevMonth::from_u8(1, DateOffset::BusinessDays(-1));

    let backtest_start = NaiveDate::from_ymd_opt(2024, 1, 1).unwrap();
    let backtest_end = NaiveDate::from_ymd_opt(2026, 6, 1).unwrap();

    // Begin at a contract whose EOT is on/after backtest_start. Easy way:
    // start somewhere safely in the past and roll forward to the first
    // not-yet-expired contract.
    let seed = FuturesContract::new(
        Asset::new("GC", AssetClass::Commodity).expect("Asset got incorrect parameters"),
        Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
        Mic::xnym(),
        Currency::usd(),
        2023,
        Tenor::December,
        None,
    );
    let mut chain = FutChain::new(seed, &listing).unwrap();
    while rule.calculate(chain.contract()) < backtest_start {
        chain.advance();
    }

    println!("GC roll schedule: {backtest_start} → {backtest_end}");
    println!("{:<60} roll on", "contract");
    println!("{}", "-".repeat(80));

    let mut roll_date = rule.calculate(chain.contract());
    while roll_date < backtest_end {
        println!("{:<60} {roll_date}", chain.contract().to_string());
        chain.advance();
        roll_date = rule.calculate(chain.contract());
    }

    // The final row is the contract you'd still be holding at backtest_end.
    println!(
        "{:<60} (still active at {backtest_end})",
        chain.contract().to_string()
    );
}
