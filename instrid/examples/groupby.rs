//! Groupby:
//!     - base/price_quotation Asset
//!     - base AssetClass
//!     - instrument class
//!     - MIC
//!
//! We will make a simple Fill struct to demonstrate groupby
//!
//! Run with: `cargo run --example groupby`

use std::collections::HashMap;

use instrid::prelude::*;
use tradeprim::currency::Currency;

fn main() {
    // --- Instruments you trade
    let aapl_xnas = Instrument::Stock(Stock::new(
        Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
        Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
        Mic::xnas(),
        Currency::usd(),
    ));
    let aapl_xlon = Instrument::Stock(Stock::new(
        Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
        Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
        Mic::xlon(),
        Currency::usd(),
    ));
    let es_cme = Instrument::Futures(FuturesContract::new(
        Asset::new("ES", AssetClass::Index).expect("Asset got incorrect parameters"),
        Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
        Mic::xcme(),
        Currency::usd(),
        2026,
        Tenor::June,
        None,
    ));
    let fdax_eurex = Instrument::Futures(FuturesContract::new(
        Asset::new("FDX", AssetClass::Index).expect("Asset got incorrect parameters"),
        Asset::new("EUR", AssetClass::Currency).expect("Asset got incorrect parameters"),
        Mic::xeur(),
        Currency::eur(),
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
        Asset::new("XAU", AssetClass::Commodity).expect("Asset got incorrect parameters"),
        Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
        Mic::xlbm(),
        Currency::usd(),
    ));
    // Same LBMA gold, quoted in EUR by the FX desk.
    let xau_eur = Instrument::Stock(Stock::new(
        Asset::new("XAU", AssetClass::Commodity).expect("Asset got incorrect parameters"),
        Asset::new("EUR", AssetClass::Currency).expect("Asset got incorrect parameters"),
        Mic::xlbm(),
        Currency::eur(),
    ));
    // Shanghai Gold Exchange, CNY (onshore yuan). Materially different
    // market from LBMA due to China's capital controls — the Shanghai-London
    // spread is a real, tradable basis, not a quote conversion.
    let xau_cny = Instrument::Stock(Stock::new(
        Asset::new("XAU", AssetClass::Commodity).expect("Asset got incorrect parameters"),
        Asset::new("CNY", AssetClass::Currency).expect("Asset got incorrect parameters"),
        Mic::xsge(),
        Currency::from_alphabetic_code("CNY").expect("Could not find currency code"),
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
        "**signed cashflow by base**:\n{:#?}",
        signed_cashflow_by_base(&fills)
    );
    println!(
        "**signed cashflow by quote**:\n{:#?}",
        signed_cashflow_by_quote(&fills)
    );
    println!(
        "**fills grouped by asset class**:\n{:#?}",
        fills_by_asset_class(&fills)
    );
    println!(
        "**signed cashflow by asset class**:\n{:#?}",
        signed_cashflow_by_asset_class(&fills)
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

    /// Signed cashflow
    ///
    ///- Positive cashflow = cash into your account (you received money) → selling
    ///- Negative cashflow = cash out of your account (you paid money) → buying
    ///
    /// When the sum of quantities is zero, this is realized pnl.
    pub fn signed_cashflow(&self) -> f64 {
        -self.quantity as f64 * self.price
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
        let price_quotation = fill.instrument.price_quotation();

        *cashflow_by_base
            .entry(base)
            .or_insert(HashMap::<&'a Asset, f64>::new())
            .entry(price_quotation)
            .or_insert(0.0) += fill.signed_cashflow();
    }

    cashflow_by_base
}

/// Groups by price_quotation asset.
pub fn signed_cashflow_by_quote<'a>(
    fills: &[Fill<'a>],
) -> HashMap<&'a Asset, HashMap<&'a Asset, f64>> {
    let mut cashflow_by_quote = HashMap::new();
    for fill in fills {
        let base = fill.instrument.base();
        let price_quotation = fill.instrument.price_quotation();

        *cashflow_by_quote
            .entry(price_quotation)
            .or_insert(HashMap::<&'a Asset, f64>::new())
            .entry(base)
            .or_insert(0.0) += fill.signed_cashflow();
    }

    cashflow_by_quote
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

/// Groups cashflow by asset class and price_quotation asset.
pub fn signed_cashflow_by_asset_class<'a>(
    fills: &[Fill<'a>],
) -> HashMap<(AssetClass, &'a Asset), f64> {
    let mut grouped = HashMap::new();

    for fill in fills {
        let base_class = fill.instrument.base().class();
        let price_quotation = fill.instrument.price_quotation();

        *grouped.entry((base_class, price_quotation)).or_insert(0.0) += fill.signed_cashflow();
    }

    grouped
}
