use std::fmt::{Debug, Display};

use crate::{asset::Asset, mic::Mic};

pub mod futures;
pub mod options;
pub mod stock;

pub use futures::FuturesContract;
pub use options::{ExerciseStyle, OptionContract, OptionKind};
pub use stock::Stock;
use tradeprim::currency::Currency;

use crate::tenor::Tenor;

/// Represents a trading instrument.
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[cfg_attr(feature = "serde", serde(tag = "type"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Instrument {
    Stock(Stock),
    Futures(FuturesContract),
    Option(OptionContract),
}

/// Trait that shows that an `Instrument` is uniquely identified in the most general way.
///
/// It basically means:
///     - We buy `base` asset
///     - Using `price_quotation`
///     - On `mic` venue
///     - using `settlement_currency`
pub trait TradedInstrument {
    /// Returns a reference to the base asset of this instrument.
    fn base(&self) -> &Asset;
    /// Returns a reference to the price quotation asset of this instrument.
    fn price_quotation(&self) -> &Asset;
    /// Returns a reference to the MIC of this instrument.
    fn mic(&self) -> &Mic;
    /// Returns a settlement currency.
    fn settlement_currency(&self) -> &Currency;
}

impl TradedInstrument for Instrument {
    fn base(&self) -> &Asset {
        match self {
            Instrument::Stock(stock) => stock.base(),
            Instrument::Futures(futures) => futures.base(),
            Instrument::Option(option) => option.base(),
        }
    }

    fn price_quotation(&self) -> &Asset {
        match self {
            Instrument::Stock(stock) => stock.price_quotation(),
            Instrument::Futures(futures) => futures.price_quotation(),
            Instrument::Option(option) => option.price_quotation(),
        }
    }

    fn mic(&self) -> &Mic {
        match self {
            Instrument::Stock(stock) => stock.mic(),
            Instrument::Futures(futures) => futures.mic(),
            Instrument::Option(option) => option.mic(),
        }
    }

    fn settlement_currency(&self) -> &Currency {
        match self {
            Instrument::Stock(stock) => stock.settlement_currency(),
            Instrument::Futures(futures) => futures.settlement_currency(),
            Instrument::Option(option) => option.settlement_currency(),
        }
    }
}

impl From<Stock> for Instrument {
    fn from(s: Stock) -> Self {
        Self::Stock(s)
    }
}

impl From<FuturesContract> for Instrument {
    fn from(c: FuturesContract) -> Self {
        Self::Futures(c)
    }
}

impl From<OptionContract> for Instrument {
    fn from(o: OptionContract) -> Self {
        Self::Option(o)
    }
}

impl Display for Instrument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instrument::Stock(s) => std::fmt::Display::fmt(s, f),
            Instrument::Futures(fu) => std::fmt::Display::fmt(fu, f),
            Instrument::Option(option) => std::fmt::Display::fmt(option, f),
        }
    }
}

/// A struct representing an invalid contract date returned by Instrument constructors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidContractDate {
    pub year: u16,
    pub tenor: Tenor,
    pub day: Option<u8>,
}

impl std::error::Error for InvalidContractDate {}

impl Display for InvalidContractDate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.day {
            Some(day) => write!(
                f,
                "invalid contract date: {:04}-{:02}-{:02}",
                self.year,
                self.tenor.ordinal(),
                day
            ),
            None => write!(
                f,
                "invalid contract date: {:04}-{:02}",
                self.year,
                self.tenor.ordinal()
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use std::str::FromStr;

    #[cfg(feature = "serde")]
    use tradeprim::price::Price;

    #[cfg(feature = "serde")]
    use crate::_assert_owned;
    use crate::asset::AssetClass;
    use crate::mic::MicIso;
    #[cfg(feature = "serde")]
    use crate::tenor::Tenor;

    use super::*;

    fn aapl_stock() -> Stock {
        Stock::new(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            MicIso::xnas().into(),
            Currency::usd(),
        )
    }

    #[cfg(feature = "serde")]
    fn cl_future() -> FuturesContract {
        FuturesContract::new_unchecked(
            Asset::new("CL", AssetClass::Commodity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            MicIso::xnas().into(),
            Currency::usd(),
            2026,
            Tenor::June,
            None,
        )
    }

    #[cfg(feature = "serde")]
    fn aapl_option() -> OptionContract {
        OptionContract::new_unchecked(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            Currency::usd(),
            2025,
            Tenor::December,
            19,
            OptionKind::Call,
            ExerciseStyle::American,
            Price::from_str("200.00").unwrap(),
        )
    }

    #[test]
    fn from_stock_into_instrument() {
        let inst: Instrument = aapl_stock().into();
        assert!(matches!(inst, Instrument::Stock(_)));
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_stock_serialize() {
        let inst: Instrument = aapl_stock().into();
        let serialized = serde_json::to_string(&inst).unwrap();
        let expected = "{\"type\":\"Stock\",\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\"}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_stock_deserialize() {
        let serialized = "{\"type\":\"Stock\",\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\"}";
        let expected: Instrument = aapl_stock().into();
        let deserialized: Instrument = serde_json::from_str(serialized).unwrap();

        assert_eq!(deserialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_futures_serialize() {
        let inst: Instrument = cl_future().into();
        let serialized = serde_json::to_string(&inst).unwrap();
        let expected = "{\"type\":\"Futures\",\"base\":{\"name\":\"CL\",\"class\":\"Commodity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2026,\"tenor\":6,\"day\":null}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_futures_deserialize() {
        let serialized = "{\"type\":\"Futures\",\"base\":{\"name\":\"CL\",\"class\":\"Commodity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2026,\"tenor\":6,\"day\":null}";
        let expected: Instrument = cl_future().into();
        let deserialized: Instrument = serde_json::from_str(serialized).unwrap();

        assert_eq!(deserialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_option_serialize() {
        let inst: Instrument = aapl_option().into();
        let serialized = serde_json::to_string(&inst).unwrap();
        let expected = "{\"type\":\"Option\",\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2025,\"tenor\":12,\"day\":19,\"kind\":\"Call\",\"style\":\"American\",\"strike\":\"200\"}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_option_deserialize() {
        let serialized = "{\"type\":\"Option\",\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2025,\"tenor\":12,\"day\":19,\"kind\":\"Call\",\"style\":\"American\",\"strike\":\"200\"}";
        let expected: Instrument = aapl_option().into();
        let deserialized: Instrument = serde_json::from_str(serialized).unwrap();

        assert_eq!(deserialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_is_owned() {
        _assert_owned::<Instrument>();
    }
}
