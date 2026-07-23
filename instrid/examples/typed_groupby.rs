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
    Side, currency::Currency, currency_notional::CurrencyNotional, price::Price, quantity::Quantity,
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
    ) = create_specs();

    let mut registry = Registry::new();
    registry.register(AAPL_XNAS, aapl_xnas_spec);
    registry.register(AAPL_XLON, aapl_xlon_spec);
    registry.register(ES_CME, es_cme_spec);
    registry.register(FDAX_EUREX, fdax_eurex_spec);
    registry.register(XAU_USD, xau_usd_spec);
    registry.register(XAU_EUR, xau_eur_spec);
    registry.register(XAU_CHF, xau_chf_spec);
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
const ES_CME: Instrument = Instrument::Futures(FuturesContract::new(
    unwrap_asset(Asset::new("ES", AssetClass::Index)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xcme(),
    Currency::usd(),
    2026,
    Tenor::June,
    None,
));
const FDAX_EUREX: Instrument = Instrument::Futures(FuturesContract::new(
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
// ---

fn create_specs() -> (
    Specification,
    Specification,
    Specification,
    Specification,
    Specification,
    Specification,
    Specification,
) {
    let aapl_xnas_spec: Specification = Specification::default();
    let aapl_xlon_spec: Specification = Specification::default();
    let es_cme_spec: Specification = Specification::new(
        Price::from_str_unchecked("0.25"),
        (Price::from_str_unchecked("12.5"), Currency::usd().into()),
    )
    .unwrap();
    let fdax_eurex_spec: Specification = Specification::new(
        Price::from_str_unchecked("1.0"),
        (Price::from_str_unchecked("25.0"), Currency::eur().into()),
    )
    .unwrap();
    let xau_usd_spec: Specification = Specification::default();
    let xau_eur_spec: Specification = Specification::new(
        Price::from_str_unchecked("0.01"),
        (Price::from_str_unchecked("0.01"), Currency::eur().into()),
    )
    .unwrap();
    let xau_chf_spec: Specification = Specification::new(
        Price::from_str_unchecked("0.01"),
        (Price::from_str_unchecked("0.01"), Currency::chf().into()),
    )
    .unwrap();

    (
        aapl_xnas_spec,
        aapl_xlon_spec,
        es_cme_spec,
        fdax_eurex_spec,
        xau_usd_spec,
        xau_eur_spec,
        xau_chf_spec,
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
