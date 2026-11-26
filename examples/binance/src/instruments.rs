//! The instruments the bins trade, written by hand from Binance's filters
//! (`GET /api/v3/exchangeInfo`). They are the same on testnet, demo and live.
//!
//! Not in [`Specification`]: every order must also be worth at least 5 in the quote asset
//! (the `NOTIONAL` filter). The minimum quantity alone doesn't guarantee it: 0.00001 BTC is
//! about 1 USDT.

use instrid::prelude::{Asset, Crypto, Instrument, Mic};
use instrid::spec::Specification;
use tradeprim::currency::Currency;
use tradeprim::price::Price;
use tradeprim::quantity::{QtyStep, Quantity};

/// An instrument with its Binance symbol and specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Listed {
    /// What the API calls it, e.g. `BTCUSDT`.
    pub symbol: &'static str,
    pub instrument: Instrument,
    pub spec: Specification,
}

pub fn btc_usdt() -> Listed {
    spot(
        "BTCUSDT",
        crypto("BTC"),
        crypto("USDT"),
        "0.01",
        "0.00001",
        "9000",
    )
}

pub fn eth_usdt() -> Listed {
    spot(
        "ETHUSDT",
        crypto("ETH"),
        crypto("USDT"),
        "0.01",
        "0.0001",
        "9000",
    )
}

pub fn bnb_usdt() -> Listed {
    spot(
        "BNBUSDT",
        crypto("BNB"),
        crypto("USDT"),
        "0.01",
        "0.001",
        "900000",
    )
}

/// Settles in a fiat currency.
pub fn btc_eur() -> Listed {
    spot(
        "BTCEUR",
        crypto("BTC"),
        Currency::eur().into(),
        "0.01",
        "0.00001",
        "9000",
    )
}

pub fn all() -> [Listed; 4] {
    [btc_usdt(), eth_usdt(), bnb_usdt(), btc_eur()]
}

/// The listed instrument with this Binance symbol.
pub fn by_symbol(symbol: &str) -> Option<Listed> {
    all().into_iter().find(|listed| listed.symbol == symbol)
}

fn crypto(name: &str) -> Asset {
    Asset::crypto(name).expect("a short ASCII name")
}

/// A spot pair on Binance (no MIC). One tick of price is worth one tick of the quote, and the
/// minimum quantity is the step (`LOT_SIZE`'s `minQty == stepSize` for every pair here).
fn spot(
    symbol: &'static str,
    base: Asset,
    quote: Asset,
    tick: &str,
    step: &str,
    max: &str,
) -> Listed {
    let tick = Price::from_str_unchecked(tick);
    let step = Quantity::from_str_unchecked(step);
    let instrument = Crypto::new(base, quote, Mic::xxxx())
        .expect("one side is crypto")
        .into();
    let spec = Specification::new(
        tick,
        (tick, quote),
        step,
        Quantity::from_str_unchecked(max),
        QtyStep::new(step).expect("a positive step"),
    )
    .expect("a valid specification");
    Listed {
        symbol,
        instrument,
        spec,
    }
}

#[cfg(test)]
mod tests {
    use instrid::prelude::TradedInstrument;
    use instrid::spec::{PointValue, Spec};

    use super::*;

    /// Catches a symbol that doesn't match its assets, e.g. `ETHUSDT` built from BTC.
    #[test]
    fn each_symbol_is_its_base_and_quote() {
        for listed in all() {
            let i = listed.instrument;
            assert_eq!(
                listed.symbol,
                format!("{}{}", i.base().name(), i.price_quotation().name())
            );
        }
    }

    #[test]
    fn btc_eur() {
        let listed = super::btc_eur();
        assert_eq!(
            listed.instrument.to_string(),
            "Crypto:Crypto|BTC/Currency|EUR@XXXX"
        );
        assert_eq!(
            listed.instrument.settlement(),
            &Asset::currency(Currency::eur())
        );
        assert_eq!(listed.spec.point_value(), PointValue::ONE);
        assert!(
            listed
                .spec
                .is_qty_valid(Quantity::from_str_unchecked("0.00006"))
        );
        assert!(
            !listed
                .spec
                .is_qty_valid(Quantity::from_str_unchecked("0.000005"))
        );
    }

    #[test]
    fn by_symbol_finds_a_listed_one() {
        assert_eq!(by_symbol("ETHUSDT"), Some(eth_usdt()));
        assert_eq!(by_symbol("XRPUSDT"), None);
    }
}
