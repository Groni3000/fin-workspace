//! Find today's active futures contract by walking a chain forward.
//!
//! The chain itself doesn't know about dates — it only knows the listing
//! cycle. An [`EndOfTrading`] rule supplies the calendar logic. Combine them
//! with a `while` loop: roll forward as long as the cursor's EOT is in the
//! past.
//!
//! Run with: `cargo run --example find_active_contract`

use chrono::{NaiveDate, Weekday};
use futchain::{
    EndOfTrading, FutChain, ListedTenors,
    eot::{DateOffset, NthInMonth, NthWeekdayOfCurrentMonth},
};
use instrid::prelude::{Asset, AssetClass, FuturesContract, MicIso, Tenor};
use tradeprim::currency::Currency;

fn main() {
    // ES (E-mini S&P 500):
    //   - listed in the quarterly cycle (Mar, Jun, Sep, Dec)
    //   - terminates on the 3rd Friday of the contract month
    //   - we apply -1 BDay defensive offset (avoid trading on termination day)
    let listing = ListedTenors::new(vec![
        Tenor::March,
        Tenor::June,
        Tenor::September,
        Tenor::December,
    ])
    .unwrap();

    let rule = NthWeekdayOfCurrentMonth {
        n: NthInMonth::Third,
        weekday: Weekday::Fri,
        offset: DateOffset::BusinessDays(-1),
    };

    // Start at a known-historical front month. Conservative: pick something
    // we know is in the past relative to `today`.
    let start = FuturesContract::new(
        Asset::new("ES", AssetClass::Index).expect("Asset got incorrect parameters"),
        Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
        MicIso::xcme(),
        Currency::usd(),
        2024,
        Tenor::December,
        None,
    );

    let today = NaiveDate::from_ymd_opt(2026, 5, 13).unwrap();
    let mut chain = FutChain::new(start, &listing).unwrap();

    println!("Today: {today}");
    println!("Starting cursor: {}", chain.contract());
    println!();

    // The core loop: walk forward until the cursor's EOT is on/after today.
    while rule.calculate(chain.contract()) < today {
        let eot = rule.calculate(chain.contract());
        println!("  expired on {eot}: {}", chain.contract());
        chain.advance();
    }

    let active_eot = rule.calculate(chain.contract());
    println!();
    println!("Active contract: {}", chain.contract());
    println!("  EOT: {active_eot}");
}
