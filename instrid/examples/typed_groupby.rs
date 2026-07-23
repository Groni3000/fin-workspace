// This file is created to test the usage of new `tradeprim` types.

use instrid::{
    asset::{Asset, AssetClass},
    inline_str::InlineStrError,
    instruments::{FuturesContract, Instrument, Stock},
    mic::Mic,
    spec::Specification,
    tenor::Tenor,
};
use tradeprim::{Side, currency::Currency, price::Price, quantity::Quantity};

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
const aapl_xnas: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("AAPL", AssetClass::Equity)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xnas(),
    Currency::usd(),
));
const aapl_xlon: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("AAPL", AssetClass::Equity)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xlon(),
    Currency::usd(),
));
const es_cme: Instrument = Instrument::Futures(FuturesContract::new(
    unwrap_asset(Asset::new("ES", AssetClass::Index)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xcme(),
    Currency::usd(),
    2026,
    Tenor::June,
    None,
));
const fdax_eurex: Instrument = Instrument::Futures(FuturesContract::new(
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
const xau_usd: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("XAU", AssetClass::Commodity)),
    unwrap_asset(Asset::new("USD", AssetClass::Currency)),
    Mic::xlbm(),
    Currency::usd(),
));
// Same LBMA gold, quoted in EUR by the FX desk.
const xau_eur: Instrument = Instrument::Stock(Stock::new(
    unwrap_asset(Asset::new("XAU", AssetClass::Commodity)),
    unwrap_asset(Asset::new("EUR", AssetClass::Currency)),
    Mic::xlbm(),
    Currency::eur(),
));
// Shanghai Gold Exchange, CNY (onshore yuan). Materially different
// market from LBMA due to China's capital controls — the Shanghai-London
// spread is a real, tradable basis, not a quote conversion.
const xau_chf: Instrument = Instrument::Stock(Stock::new(
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
}
