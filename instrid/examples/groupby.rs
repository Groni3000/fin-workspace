//! Groupby:
//!     - base/quote Asset
//!     - base AssetClass
//!     - instrument class
//!     - MIC
//!
//! We will make a simple Fill struct to demonstrate groupby
//!
//! Run with: `cargo run --example groupby`

use std::collections::HashMap;

use instrid::prelude::*;

fn main() {
    // --- Instruments you trade
    let aapl_xnas = Instrument::Stock(Stock::new(
        Asset::new("AAPL", AssetClass::Equity),
        Asset::new("USD", AssetClass::Currency),
        Mic::xnas(),
    ));
    let aapl_xlon = Instrument::Stock(Stock::new(
        Asset::new("AAPL", AssetClass::Equity),
        Asset::new("USD", AssetClass::Currency),
        Mic::xlon(),
    ));
    let es_cme = Instrument::Futures(FuturesContract::new(
        Asset::new("ES", AssetClass::Index),
        Asset::new("USD", AssetClass::Currency),
        Mic::xcme(),
        2026,
        Tenor::June,
        None,
    ));
    let fdax_eurex = Instrument::Futures(FuturesContract::new(
        Asset::new("FDX", AssetClass::Index),
        Asset::new("EUR", AssetClass::Currency),
        Mic::xeur(),
        2026,
        Tenor::June,
        None,
    ));
    // Spot gold: same base entity (XAU), three different quote currencies.
    // We abuse the Stock model because:
    //  - Commodity Spot is not implemented (yet?)
    //  - We don't care about Delivery Location right now.

    // Canonical XAU quote: LBMA Gold Price, USD.
    let xau_usd = Instrument::Stock(Stock::new(
        Asset::new("XAU", AssetClass::Commodity),
        Asset::new("USD", AssetClass::Currency),
        Mic::xlbm(),
    ));
    // Same LBMA gold, quoted in EUR by the FX desk.
    let xau_eur = Instrument::Stock(Stock::new(
        Asset::new("XAU", AssetClass::Commodity),
        Asset::new("EUR", AssetClass::Currency),
        Mic::xlbm(),
    ));
    // Shanghai Gold Exchange, CNY (onshore yuan). Materially different
    // market from LBMA due to China's capital controls — the Shanghai-London
    // spread is a real, tradable basis, not a quote conversion.
    let xau_cny = Instrument::Stock(Stock::new(
        Asset::new("XAU", AssetClass::Commodity),
        Asset::new("CNY", AssetClass::Currency),
        Mic::xsge(),
    ));
    // ---

    // --- Historical fills
    let fills = vec![
        Fill::new(&aapl_xnas, 1, 300.0),
        Fill::new(&aapl_xlon, -1, 300.34),
        Fill::new(&aapl_xnas, -1, 300.19),
        Fill::new(&aapl_xlon, 1, 300.24),
        Fill::new(&es_cme, 1, 24_000.0),
        // FDAX is traded in EUR.
        Fill::new(&fdax_eurex, -3, 40_000.0),
        // XAU in three different quote currencies —
        // the same gold, priced three different ways.
        Fill::new(&xau_usd, 10, 2_650.0),
        Fill::new(&xau_usd, -4, 2_661.5),
        Fill::new(&xau_eur, 5, 2_440.0),
        Fill::new(&xau_cny, 2, 410_000.0),
    ];
    // ---

    println!(
        "**signed cashflow**:\n{:#?}",
        signed_cashflow_by_base(&fills)
    );
    println!("**grouped by quote**:\n{:#?}", grouped_by_quote(&fills));
    println!(
        "**grouped by asset class**:\n{:#?}",
        fills_by_asset_class(&fills)
    );
    println!(
        "**cashflow by asset class**:\n{:#?}",
        cashflow_by_asset_class(&fills)
    );
}

/// Simple struct representing a fill on an instrument.
///
/// Just for demonstration purposes.
#[derive(Debug)]
pub struct Fill<'a> {
    instrument: &'a Instrument,
    quantity: i32,
    price: f64,
}

impl<'a> Fill<'a> {
    pub fn new(instrument: &'a Instrument, quantity: i32, price: f64) -> Self {
        Self {
            instrument,
            quantity,
            price,
        }
    }
}

// --- Groupby demo function|

/// Groups signed cashflow by base asset.
///
/// For groups whose **net quantity is zero**, cashflow **equals realized P&L**.
pub fn signed_cashflow_by_base<'a>(
    fills: &[Fill<'a>],
) -> HashMap<&'a Asset, HashMap<&'a Asset, f64>> {
    let mut cashflow_by_base = HashMap::new();
    for fill in fills {
        let base = fill.instrument.base();
        let quote = fill.instrument.quote();
        let cashflow = fill.quantity as f64 * fill.price;

        *cashflow_by_base
            .entry(base)
            .or_insert(HashMap::<&'a Asset, f64>::new())
            .entry(quote)
            .or_insert(0.0) += cashflow;
    }

    cashflow_by_base
}

/// Groups by quote asset.
pub fn grouped_by_quote<'a>(fills: &[Fill<'a>]) -> HashMap<&'a Asset, HashMap<&'a Asset, f64>> {
    let mut cashflow_by_base = HashMap::new();
    for fill in fills {
        let base = fill.instrument.base();
        let quote = fill.instrument.quote();
        let cashflow = fill.quantity as f64 * fill.price;

        *cashflow_by_base
            .entry(quote)
            .or_insert(HashMap::<&'a Asset, f64>::new())
            .entry(base)
            .or_insert(0.0) += cashflow;
    }

    cashflow_by_base
}

/// Just bucketing fills by asset class.
pub fn fills_by_asset_class<'a, 'b>(
    fills: &'b [Fill<'a>],
) -> HashMap<AssetClass, Vec<&'b Fill<'a>>> {
    let mut grouped = HashMap::new();

    for fill in fills.iter() {
        let base = fill.instrument.base();
        let class = base.class();

        grouped.entry(class).or_insert_with(Vec::new).push(fill);
    }

    grouped
}

pub fn cashflow_by_asset_class<'a>(fills: &[Fill<'a>]) -> HashMap<(AssetClass, &'a Asset), f64> {
    let mut grouped = HashMap::new();

    for fill in fills {
        let base_class = fill.instrument.base().class();
        let quote = fill.instrument.quote();
        let cashflow = fill.quantity as f64 * fill.price;

        *grouped.entry((base_class, quote)).or_insert(0.0) += cashflow;
    }

    grouped
}
