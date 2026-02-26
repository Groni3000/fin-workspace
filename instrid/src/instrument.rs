use crate::{
    asset::{Asset, AssetParseError},
    exchange::{Exchange, ExchangeParseError},
};
use std::fmt;
use std::str::FromStr;

/// A base trading instrument identified by a base asset, quote asset, and exchange.
///
/// This is the fundamental building block for all instrument types in this library.
/// More specific instrument types (`Stock`, `Future`, `OptionContract`) embed this struct.
///
/// # Examples
/// ```
/// use instrid::instrument::Instrument;
/// use instrid::asset::Asset;
/// use instrid::exchange::Exchange;
///
/// // Compile-time constant
/// const inst: Instrument = Instrument::new(Asset::BTC, Asset::USDT, Exchange::BINANCE);
///
/// // Runtime parsing
/// let inst: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Instrument {
    pub base: Asset,
    pub quote: Asset,
    pub exchange: Exchange,
}

impl Instrument {
    /// Creates a new `Instrument` from its components.
    ///
    /// Intended for use in `const` contexts. For runtime construction from strings,
    /// use `FromStr` instead:
    /// ```
    /// let inst: Instrument = "BTC/USDT@BINANCE".parse()?;
    /// ```
    pub const fn new(base: Asset, quote: Asset, exchange: Exchange) -> Self {
        Self {
            base,
            quote,
            exchange,
        }
    }
}

/// Error returned when parsing an `Instrument` from a string fails.
#[derive(Debug)]
pub enum InstrumentParseError {
    /// The overall format was not `BASE/QUOTE@EXCHANGE`
    InvalidFormat,
    InvalidBase(AssetParseError),
    InvalidQuote(AssetParseError),
    InvalidExchange(ExchangeParseError),
}

impl fmt::Display for InstrumentParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InstrumentParseError::InvalidFormat => write!(
                f,
                "invalid instrument format (expected BASE/QUOTE@EXCHANGE, e.g. BTC/USDT@BINANCE)"
            ),
            InstrumentParseError::InvalidBase(e) => write!(f, "invalid base asset: {}", e),
            InstrumentParseError::InvalidQuote(e) => write!(f, "invalid quote asset: {}", e),
            InstrumentParseError::InvalidExchange(e) => write!(f, "invalid exchange: {}", e),
        }
    }
}

impl std::error::Error for InstrumentParseError {}

impl FromStr for Instrument {
    type Err = InstrumentParseError;

    /// Parses an `Instrument` from a string in the format `BASE/QUOTE@EXCHANGE`.
    ///
    /// # Examples
    /// ```
    /// let inst: Instrument = "BTC/USDT@BINANCE".parse()?;
    /// let inst: Instrument = "EUR/USD@NYSE".parse()?;
    /// ```
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (pair, exchange) = s
            .split_once('@')
            .ok_or(InstrumentParseError::InvalidFormat)?;

        let (base, quote) = pair
            .split_once('/')
            .ok_or(InstrumentParseError::InvalidFormat)?;

        let base = base
            .parse::<Asset>()
            .map_err(InstrumentParseError::InvalidBase)?;
        let quote = quote
            .parse::<Asset>()
            .map_err(InstrumentParseError::InvalidQuote)?;
        let exchange = exchange
            .parse::<Exchange>()
            .map_err(InstrumentParseError::InvalidExchange)?;

        Ok(Instrument::new(base, quote, exchange))
    }
}

impl fmt::Display for Instrument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{} @ {}", self.base, self.quote, self.exchange)
    }
}

/// Core trait implemented by all instrument types in this library.
pub trait TradeInstrument {
    fn base(&self) -> &Asset;
    fn quote(&self) -> &Asset;
    fn exchange(&self) -> &Exchange;
}

impl TradeInstrument for Instrument {
    fn base(&self) -> &Asset {
        &self.base
    }
    fn quote(&self) -> &Asset {
        &self.quote
    }
    fn exchange(&self) -> &Exchange {
        &self.exchange
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // region: FromStr

    #[test]
    fn parse_valid_traditional() {
        let inst: Instrument = "EUR/USD@NYSE".parse().unwrap();
        assert_eq!(inst.base, Asset::EUR);
        assert_eq!(inst.quote, Asset::USD);
        assert_eq!(inst.exchange, Exchange::NYSE);
    }

    #[test]
    fn parse_valid_crypto() {
        let inst: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
        assert_eq!(inst.base.code(), "BTC");
        assert_eq!(inst.quote.code(), "USDT");
        assert_eq!(inst.exchange.code(), "BINANCE");
    }

    #[test]
    fn parse_missing_slash() {
        let result = "EURUSD@NYSE".parse::<Instrument>();
        assert!(matches!(result, Err(InstrumentParseError::InvalidFormat)));
    }

    #[test]
    fn parse_missing_at() {
        let result = "EUR/USDNYSE".parse::<Instrument>();
        assert!(matches!(result, Err(InstrumentParseError::InvalidFormat)));
    }

    #[test]
    fn parse_empty_string() {
        let result = "".parse::<Instrument>();
        assert!(matches!(result, Err(InstrumentParseError::InvalidFormat)));
    }

    #[test]
    fn parse_invalid_base() {
        let result = "eur/USD@NYSE".parse::<Instrument>();
        assert!(matches!(result, Err(InstrumentParseError::InvalidBase(_))));
    }

    #[test]
    fn parse_invalid_quote() {
        let result = "EUR/usd@NYSE".parse::<Instrument>();
        assert!(matches!(result, Err(InstrumentParseError::InvalidQuote(_))));
    }

    #[test]
    fn parse_invalid_exchange() {
        let result = "EUR/USD@nyse".parse::<Instrument>();
        assert!(matches!(
            result,
            Err(InstrumentParseError::InvalidExchange(_))
        ));
    }

    #[test]
    fn parse_empty_base() {
        let result = "/USD@NYSE".parse::<Instrument>();
        assert!(matches!(result, Err(InstrumentParseError::InvalidBase(_))));
    }

    #[test]
    fn parse_empty_quote() {
        let result = "EUR/@NYSE".parse::<Instrument>();
        assert!(matches!(result, Err(InstrumentParseError::InvalidQuote(_))));
    }

    #[test]
    fn parse_empty_exchange() {
        let result = "EUR/USD@".parse::<Instrument>();
        assert!(matches!(
            result,
            Err(InstrumentParseError::InvalidExchange(_))
        ));
    }

    // endregion

    // region: Display / round-trip

    #[test]
    fn display_format() {
        let inst: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
        assert_eq!(inst.to_string(), "BTC/USDT @ BINANCE");
    }

    #[test]
    fn roundtrip() {
        // Display adds spaces around @, so round-trip needs to account for that
        // This test documents current behavior explicitly
        let original = Instrument::new(Asset::EUR, Asset::USD, Exchange::NYSE);
        let displayed = original.to_string(); // "EUR/USD @ NYSE"
        // spaces around @ break naive round-trip — this is intentional,
        // parse format is strict: no spaces
        assert!(displayed.parse::<Instrument>().is_err());
    }

    // endregion

    // region: const construction

    #[test]
    fn const_construction() {
        const INST: Instrument = Instrument::new(Asset::EUR, Asset::USD, Exchange::CME);
        assert_eq!(INST.base, Asset::EUR);
        assert_eq!(INST.quote, Asset::USD);
        assert_eq!(INST.exchange, Exchange::CME);
    }

    // endregion

    // region: equality and hashing

    #[test]
    fn equality() {
        let a: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
        let b: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn inequality_different_exchange() {
        let a: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
        let b: Instrument = "BTC/USDT@NYSE".parse().unwrap();
        assert_ne!(a, b);
    }

    #[test]
    fn inequality_different_quote() {
        let a: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
        let b: Instrument = "BTC/USDC@BINANCE".parse().unwrap();
        assert_ne!(a, b);
    }

    #[test]
    fn usable_as_hashmap_key() {
        use std::collections::HashMap;
        let mut map: HashMap<Instrument, f64> = HashMap::new();
        let inst: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
        map.insert(inst, 42000.0);
        let inst2: Instrument = "BTC/USDT@BINANCE".parse().unwrap();
        assert_eq!(map[&inst2], 42000.0);
    }

    // endregion
}
