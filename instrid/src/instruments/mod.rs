use std::fmt::{Debug, Display};

use crate::{asset::Asset, mic::Mic};

pub mod futures;
pub mod options;
pub mod stock;

pub use futures::FuturesContract;
pub use options::{ExerciseStyle, OptionContract, OptionKind};
pub use stock::Stock;

/// Represents a trading instrument.
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[cfg_attr(feature = "serde", serde(tag = "type"))]
#[derive(Debug, PartialEq, Eq)]
pub enum Instrument {
    Stock(Stock),
    Futures(FuturesContract),
    Option(OptionContract),
}

/// Trait that shows that an `Instrument` is uniquely identified in the most general way.
///
/// It basically means:
///     - We buy `base` asset
///     - Using `quote` asset
///     - On `mic` venue
pub trait TradedInstrument {
    /// Returns a reference to the base asset of this instrument.
    fn base(&self) -> &Asset;
    /// Returns a reference to the quote asset of this instrument.
    fn quote(&self) -> &Asset;
    /// Returns a reference to the MIC of this instrument.
    fn mic(&self) -> &Mic;
}

impl TradedInstrument for Instrument {
    fn base(&self) -> &Asset {
        match self {
            Instrument::Stock(stock) => stock.base(),
            Instrument::Futures(futures) => futures.base(),
            Instrument::Option(option) => option.base(),
        }
    }

    fn quote(&self) -> &Asset {
        match self {
            Instrument::Stock(stock) => stock.quote(),
            Instrument::Futures(futures) => futures.quote(),
            Instrument::Option(option) => option.quote(),
        }
    }

    fn mic(&self) -> &Mic {
        match self {
            Instrument::Stock(stock) => stock.mic(),
            Instrument::Futures(futures) => futures.mic(),
            Instrument::Option(option) => option.mic(),
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

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use crate::_assert_owned;
    use crate::asset::AssetClass;
    use crate::tenor::Tenor;

    use super::*;

    #[cfg(feature = "serde")]
    use rust_decimal_macros::dec;

    fn aapl_stock() -> Stock {
        Stock::new(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
        )
    }

    fn cl_future() -> FuturesContract {
        FuturesContract::new(
            Asset::new("CL", AssetClass::Commodity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            2026,
            Tenor::June,
            None,
        )
    }

    #[cfg(feature = "serde")]
    fn aapl_option() -> OptionContract {
        OptionContract::new(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            2025,
            Tenor::December,
            19,
            OptionKind::Call,
            ExerciseStyle::American,
            dec!(200.00),
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
        let expected = "{\"type\":\"Stock\",\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"quote\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\"}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_stock_deserialize() {
        let serialized = "{\"type\":\"Stock\",\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"quote\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\"}";
        let expected: Instrument = aapl_stock().into();
        let deserialized: Instrument = serde_json::from_str(serialized).unwrap();

        assert_eq!(deserialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_futures_serialize() {
        let inst: Instrument = cl_future().into();
        let serialized = serde_json::to_string(&inst).unwrap();
        let expected = "{\"type\":\"Futures\",\"base\":{\"name\":\"CL\",\"class\":\"Commodity\"},\"quote\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"year\":2026,\"tenor\":6,\"day\":null}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_futures_deserialize() {
        let serialized = "{\"type\":\"Futures\",\"base\":{\"name\":\"CL\",\"class\":\"Commodity\"},\"quote\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"year\":2026,\"tenor\":6,\"day\":null}";
        let expected: Instrument = cl_future().into();
        let deserialized: Instrument = serde_json::from_str(serialized).unwrap();

        assert_eq!(deserialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_option_serialize() {
        let inst: Instrument = aapl_option().into();
        let serialized = serde_json::to_string(&inst).unwrap();
        let expected = "{\"type\":\"Option\",\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"quote\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"year\":2025,\"tenor\":12,\"day\":19,\"kind\":\"Call\",\"style\":\"American\",\"strike\":\"200.00\"}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_instrument_option_deserialize() {
        let serialized = "{\"type\":\"Option\",\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"quote\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"year\":2025,\"tenor\":12,\"day\":19,\"kind\":\"Call\",\"style\":\"American\",\"strike\":\"200.00\"}";
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
