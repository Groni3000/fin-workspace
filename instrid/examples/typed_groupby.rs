// This file is created to test the usage of new `tradeprim` types.

use std::collections::HashMap;

use instrid::{
    asset::{Asset, AssetClass},
    inline_str::InlineStrError,
    instruments::{FuturesContract, Instrument, Stock, TradedInstrument},
    mic::Mic,
    spec::{Spec, Specification},
    tenor::Tenor,
};
use tradeprim::{
    Side,
    currency::Currency,
    currency_notional::CurrencyNotional,
    price::Price,
    quantity::{QtyStep, Quantity},
};

fn main() {
    // Specifications can't be const created due to various checks
    //
    // It _probably_ can be const created for curated currencies, but
    // we need to add `new_unchecked`
    let (
        aapl_xnas_spec,
        aapl_xlon_spec,
        es_cme_spec,
        fdax_eurex_spec,
        xau_usd_spec,
        xau_eur_spec,
        xau_chf_spec,
        jpy_6j_spec,
        btc_usd_spec,
    ) = create_specs();

    let mut registry = Registry::new();
    registry.register(AAPL_XNAS, aapl_xnas_spec);
    registry.register(AAPL_XLON, aapl_xlon_spec);
    registry.register(ES_CME, es_cme_spec);
    registry.register(FDAX_EUREX, fdax_eurex_spec);
    registry.register(XAU_USD, xau_usd_spec);
    registry.register(XAU_EUR, xau_eur_spec);
    registry.register(XAU_CHF, xau_chf_spec);
    registry.register(JPY_6J, jpy_6j_spec);
    registry.register(BTC_USD, btc_usd_spec);

    let fills = vec![
        Fill::new(&AAPL_XNAS, Side::Buy, qty("1"), px("300.15")),
        Fill::new(&AAPL_XLON, Side::Sell, qty("1"), px("300.34")),
        Fill::new(&AAPL_XNAS, Side::Sell, qty("1"), px("300.19")),
        Fill::new(&AAPL_XLON, Side::Buy, qty("1"), px("300.24")),
        Fill::new(&ES_CME, Side::Buy, qty("1"), px("24000.25")),
        Fill::new(&FDAX_EUREX, Side::Sell, qty("3"), px("40000.50")),
        Fill::new(&FDAX_EUREX, Side::Buy, qty("3"), px("41020.50")),
        Fill::new(&XAU_USD, Side::Buy, qty("10"), px("2650.30")),
        Fill::new(&XAU_USD, Side::Sell, qty("4"), px("2661.55")),
        Fill::new(&XAU_EUR, Side::Buy, qty("5"), px("2440.75")),
        Fill::new(&XAU_CHF, Side::Buy, qty("2"), px("2400.40")),
        Fill::new(&JPY_6J, Side::Buy, qty("2"), px("0.0068155")),
        Fill::new(&JPY_6J, Side::Sell, qty("3"), px("0.0068355")),
        Fill::new(&BTC_USD, Side::Buy, qty("0.05"), px("67234.50")),
        Fill::new(&BTC_USD, Side::Sell, qty("0.05"), px("78234.50")),
        Fill::new(&ES_CME, Side::Buy, qty("1"), px("24010.00")),
        Fill::new(&ES_CME, Side::Sell, qty("1"), px("24050.00")),
        Fill::new(&ES_CME, Side::Sell, qty("1"), px("23990.00")),
        Fill::new(&XAU_USD, Side::Sell, qty("2"), px("2670.00")),
        Fill::new(&XAU_USD, Side::Sell, qty("4"), px("2655.50")),
        Fill::new(&XAU_EUR, Side::Sell, qty("2"), px("2450.00")),
        Fill::new(&XAU_EUR, Side::Sell, qty("3"), px("2445.00")),
    ];

    header("signed cashflow by currency");
    print_aligned(
        "  ",
        signed_cashflow_by_currency(&fills, &registry)
            .into_iter()
            .map(|(asset, notional)| (asset.to_string(), notional)),
    );
    println!();

    header("signed cashflow by base");
    let mut by_base: Vec<_> = signed_cashflow_by_base(&fills, &registry)
        .into_iter()
        .collect();
    by_base.sort_by(|a, b| a.0.to_string().cmp(&b.0.to_string()));
    for (base, by_quote) in by_base {
        println!("  {base}:");
        print_aligned(
            "        ",
            by_quote
                .iter()
                .map(|(quote, notional)| (quote.to_string(), *notional)),
        );
    }
    println!();

    header("fills by asset class");
    print_aligned(
        "  ",
        fills_by_asset_class(&fills)
            .into_iter()
            .map(|(class, class_fills)| {
                (class.to_string(), format!("{} fills", class_fills.len()))
            }),
    );
    println!();

    header("signed cashflow by asset class");
    print_aligned(
        "  ",
        signed_cashflow_by_asset_class(&fills, &registry)
            .into_iter()
            .map(|((class, quote), notional)| (format!("({class}, {quote})"), notional)),
    );
    println!();

    header("realized pnl per instrument (flat positions only, no FIFO/LIFO matcher yet)");
    print_aligned(
        "  ",
        realized_pnl_by_instrument_for_flat_positions(&fills, &registry)
            .into_iter()
            .map(|(instrument, pnl)| (instrument.to_string(), pnl)),
    );
}

fn header(title: &str) {
    println!("\x1b[4m{title}\x1b[0m");
}

/// To make results prettier. Sorts by key so the output is deterministic
fn print_aligned<V: std::fmt::Display>(indent: &str, rows: impl IntoIterator<Item = (String, V)>) {
    let mut rows: Vec<(String, V)> = rows.into_iter().collect();
    rows.sort_by(|a, b| a.0.cmp(&b.0));
    let width = rows
        .iter()
        .map(|(k, _)| k.chars().count())
        .max()
        .unwrap_or(0);
    for (key, value) in rows {
        println!("{indent}{key:<width$}: {value}");
    }
}

fn qty(s: &str) -> Quantity {
    Quantity::from_str_unchecked(s)
}

fn px(s: &str) -> Price {
    Price::from_str_unchecked(s)
}

// We need:
//  - Fill type - basically a placeholder for now.
//  - instruments
//  - specifications
//  - Quantity
//  - CurrencyNotional
//  - groupby functions
//
//  All values are not real, because I don't want to waste time on "real values"

// --- Instruments you trade
#[allow(dead_code)]
const fn unwrap_asset(asset: Result<Asset, InlineStrError>) -> Asset {
    match asset {
        Ok(asset) => asset,
        Err(_e) => panic!("Asset got incorrect parameters"),
    }
}
const AAPL_XNAS: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("AAPL", AssetClass::Equity)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xnas(),
    Currency::usd(),
));
const AAPL_XLON: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("AAPL", AssetClass::Equity)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xlon(),
    Currency::usd(),
));
const ES_CME: Instrument = Instrument::Futures(FuturesContract::new_unchecked(
    unwrap_asset(Asset::new("ES", AssetClass::Index)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xcme(),
    Currency::usd(),
    2026,
    Tenor::June,
    None,
));
const FDAX_EUREX: Instrument = Instrument::Futures(FuturesContract::new_unchecked(
    unwrap_asset(Asset::new("FDX", AssetClass::Index)),
    unwrap_asset(Asset::new("EUR", AssetClass::Currency)),
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
const XAU_USD: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("XAU", AssetClass::Commodity)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xlbm(),
    Currency::usd(),
));
// Same LBMA gold, quoted in EUR by the FX desk.
const XAU_EUR: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("XAU", AssetClass::Commodity)),
    unwrap_asset(Asset::new("EUR", AssetClass::Currency)),
    Mic::xlbm(),
    Currency::eur(),
));
// Shanghai Gold Exchange, CNY (onshore yuan). Materially different
// market from LBMA due to China's capital controls — the Shanghai-London
// spread is a real, tradable basis, not a quote conversion.
const XAU_CHF: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("XAU", AssetClass::Commodity)),
    unwrap_asset(Asset::new("CHF", AssetClass::Currency)),
    Mic::xsge(),
    Currency::chf(),
    // THIS CORRECT VALUE IS NOT CONST CURATED! Can't be used here.
    // So we are bullshiting right now with a not real currency for this instrument.

    // Currency::from_alphabetic_code("CNY")
    //     .expect("Code should be valid")
    //     .expect("Could not find currency code"),
));

// CME Japanese Yen future: price is USD per JPY, so the tick is tiny
// (0.0000005) and the point value is huge (12_500_000). Granular price.
const JPY_6J: Instrument = Instrument::Futures(FuturesContract::new_unchecked(
    unwrap_asset(Asset::new("JPY", AssetClass::Currency)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xcme(),
    Currency::usd(),
    2026,
    Tenor::June,
    None,
));
// Bitcoin spot in USD: whole ticks, but you trade fractional quantities.
const BTC_USD: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("BTC", AssetClass::Crypto)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::iexg(),
    Currency::usd(),
));
// ---

fn create_specs() -> (
    Specification,
    Specification,
    Specification,
    Specification,
    Specification,
    Specification,
    Specification,
    Specification,
    Specification,
) {
    let min_qty = Quantity::ONE;

    let aapl_xnas_spec: Specification = Specification::default();
    let aapl_xlon_spec: Specification = Specification::default();
    let es_cme_spec: Specification = Specification::new(
        Price::from_str_unchecked("0.25"),
        (Price::from_str_unchecked("12.5"), Currency::usd().into()),
        min_qty,
        Quantity::MAX,
        QtyStep::default(),
    )
    .unwrap();
    let fdax_eurex_spec: Specification = Specification::new(
        Price::from_str_unchecked("1.0"),
        (Price::from_str_unchecked("25.0"), Currency::eur().into()),
        min_qty,
        Quantity::MAX,
        QtyStep::default(),
    )
    .unwrap();
    let xau_usd_spec: Specification = Specification::default();
    let xau_eur_spec: Specification = Specification::new(
        Price::from_str_unchecked("0.01"),
        (Price::from_str_unchecked("0.01"), Currency::eur().into()),
        min_qty,
        Quantity::MAX,
        QtyStep::default(),
    )
    .unwrap();
    let xau_chf_spec: Specification = Specification::new(
        Price::from_str_unchecked("0.01"),
        (Price::from_str_unchecked("0.01"), Currency::chf().into()),
        min_qty,
        Quantity::MAX,
        QtyStep::default(),
    )
    .unwrap();
    let jpy_6j_spec: Specification = Specification::new(
        Price::from_str_unchecked("0.0000005"),
        (Price::from_str_unchecked("6.25"), Currency::usd().into()),
        min_qty,
        Quantity::MAX,
        QtyStep::default(),
    )
    .unwrap();
    let btc_usd_spec: Specification = Specification::default();

    (
        aapl_xnas_spec,
        aapl_xlon_spec,
        es_cme_spec,
        fdax_eurex_spec,
        xau_usd_spec,
        xau_eur_spec,
        xau_chf_spec,
        jpy_6j_spec,
        btc_usd_spec,
    )
}

/// Our own binding of instruments to their specifications.
///
/// The exchange gives us executions; the spec is reference data we own, so the
/// registry lives on our side and a `Fill` resolves its spec through it.
#[derive(Debug, Default)]
pub struct Registry {
    specs: HashMap<Instrument, Specification>,
}

impl Registry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn register(&mut self, instrument: Instrument, spec: Specification) {
        self.specs.insert(instrument, spec);
    }

    pub fn spec(&self, instrument: &Instrument) -> Option<&Specification> {
        self.specs.get(instrument)
    }
}

/// Simple placeholder fill on an instrument, using the typed `Quantity`/`Price`.
#[derive(Debug)]
pub struct Fill<'a> {
    instrument: &'a Instrument,
    side: Side,
    quantity: Quantity,
    price: Price,
}

impl<'a> Fill<'a> {
    pub fn new(instrument: &'a Instrument, side: Side, quantity: Quantity, price: Price) -> Self {
        Self {
            instrument,
            side,
            quantity,
            price,
        }
    }

    /// Signed cashflow of the fill in the instrument's settlement currency.
    ///
    /// The spec is looked up from the registry by the fill's instrument.
    pub fn signed_cashflow(&self, registry: &Registry) -> CurrencyNotional {
        let spec = registry
            .spec(self.instrument)
            .expect("instrument must be registered");
        let quote_notional = self.quantity * self.price;
        // TODO: Mul for Side and QuoteNotional?
        let signed = match self.side {
            Side::Buy => -quote_notional,
            Side::Sell => quote_notional,
        };
        spec.currency_notional(signed)
    }
}

/// Sums signed cashflow per price-quotation asset.
///
/// Each fill resolves its spec from the registry. Grouping by price-quotation
/// asset keeps one currency per bucket, so the `CurrencyNotional` `Add` never
/// has to mix currencies (it would panic otherwise).
pub fn signed_cashflow_by_currency<'a>(
    fills: &[Fill<'a>],
    registry: &Registry,
) -> HashMap<&'a Asset, CurrencyNotional> {
    let mut cashflow_by_currency = HashMap::new();
    for fill in fills {
        let price_quotation = fill.instrument.price_quotation();
        let cashflow = fill.signed_cashflow(registry);

        cashflow_by_currency
            .entry(price_quotation)
            .and_modify(|acc: &mut CurrencyNotional| *acc = *acc + cashflow)
            .or_insert(cashflow);
    }

    cashflow_by_currency
}

/// Sums signed cashflow by base asset, split by price-quotation asset.
pub fn signed_cashflow_by_base<'a>(
    fills: &[Fill<'a>],
    registry: &Registry,
) -> HashMap<&'a Asset, HashMap<&'a Asset, CurrencyNotional>> {
    let mut cashflow_by_base = HashMap::new();
    for fill in fills {
        let base = fill.instrument.base();
        let price_quotation = fill.instrument.price_quotation();
        let cashflow = fill.signed_cashflow(registry);

        cashflow_by_base
            .entry(base)
            .or_insert_with(HashMap::new)
            .entry(price_quotation)
            .and_modify(|acc: &mut CurrencyNotional| *acc = *acc + cashflow)
            .or_insert(cashflow);
    }

    cashflow_by_base
}

/// Realized P&L per instrument for flat positions.
///
/// Why only flat? Because if we want to calculate partially closed positions,
/// we need to choose a convention: FIFO (match oldest), LIFO (match newest) or... Avg?
///
/// I don't want to build a matcher right now, so... Only flat here.
pub fn realized_pnl_by_instrument_for_flat_positions<'a>(
    fills: &[Fill<'a>],
    registry: &Registry,
) -> HashMap<&'a Instrument, CurrencyNotional> {
    let mut acc: HashMap<&Instrument, (CurrencyNotional, i128)> = HashMap::new();
    for fill in fills {
        let cashflow = fill.signed_cashflow(registry);
        let signed_qty = match fill.side {
            Side::Buy => fill.quantity.value() as i128,
            Side::Sell => -(fill.quantity.value() as i128),
        };

        acc.entry(fill.instrument)
            .and_modify(|(cf, qty)| {
                *cf = *cf + cashflow;
                *qty += signed_qty;
            })
            .or_insert((cashflow, signed_qty));
    }

    acc.into_iter()
        .filter(|(_, (_, net_qty))| *net_qty == 0)
        .map(|(instrument, (cashflow, _))| (instrument, cashflow))
        .collect()
}

/// Buckets fills by the base asset's class. No summation, so no currency concern.
pub fn fills_by_asset_class<'a, 'b>(
    fills: &'b [Fill<'a>],
) -> HashMap<AssetClass, Vec<&'b Fill<'a>>> {
    let mut grouped = HashMap::new();
    for fill in fills {
        let class = fill.instrument.base().class();
        grouped.entry(class).or_insert_with(Vec::new).push(fill);
    }

    grouped
}

/// Sums signed cashflow by (base asset class, price-quotation asset).
///
/// The price-quotation asset is part of the key, so each bucket is one currency
/// and the `CurrencyNotional` `Add` never mixes currencies.
pub fn signed_cashflow_by_asset_class<'a>(
    fills: &[Fill<'a>],
    registry: &Registry,
) -> HashMap<(AssetClass, &'a Asset), CurrencyNotional> {
    let mut grouped = HashMap::new();
    for fill in fills {
        let base_class = fill.instrument.base().class();
        let price_quotation = fill.instrument.price_quotation();
        let cashflow = fill.signed_cashflow(registry);

        grouped
            .entry((base_class, price_quotation))
            .and_modify(|acc: &mut CurrencyNotional| *acc = *acc + cashflow)
            .or_insert(cashflow);
    }

    grouped
}
