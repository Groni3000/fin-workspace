use crate::{
    asset::Asset,
    exchange::Exchange,
    instrument::{Instrument, InstrumentParseError, TradeInstrument},
};
use std::fmt;
use std::str::FromStr;

/// A stock instrument, identified by its base asset, quote currency, and exchange.
///
/// This is a thin wrapper around [`Instrument`] for cases where you want to
/// distinguish stocks from other instrument types at the type level.
///
/// # Examples
/// ```
/// use instrid::stock::Stock;
/// use instrid::instrument::Instrument;
/// use instrid::asset::Asset;
/// use instrid::exchange::Exchange;
///
/// const AAPL: Stock = Stock::new(Instrument::new(Asset::new("AAPL"), Asset::USD, Exchange::NASDAQ));
///
/// let stock: Stock = "AAPL/USD@NASDAQ".parse().unwrap();
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Stock {
    pub instrument: Instrument,
}

impl Stock {
    pub const fn new(instrument: Instrument) -> Self {
        Self { instrument }
    }
}

#[derive(Debug)]
pub enum StockParseError {
    InvalidInstrument(InstrumentParseError),
}

impl fmt::Display for StockParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StockParseError::InvalidInstrument(e) => write!(f, "invalid stock: {}", e),
        }
    }
}

impl std::error::Error for StockParseError {}

impl FromStr for Stock {
    type Err = StockParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let instrument = s
            .parse::<Instrument>()
            .map_err(StockParseError::InvalidInstrument)?;
        Ok(Stock::new(instrument))
    }
}

impl fmt::Display for Stock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.instrument)
    }
}

impl TradeInstrument for Stock {
    fn base(&self) -> &Asset {
        &self.instrument.base
    }
    fn quote(&self) -> &Asset {
        &self.instrument.quote
    }
    fn exchange(&self) -> &Exchange {
        &self.instrument.exchange
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // region: FromStr

    #[test]
    fn parse_valid() {
        let stock: Stock = "AAPL/USD@NASDAQ".parse().unwrap();
        assert_eq!(stock.instrument.base.code(), "AAPL");
        assert_eq!(stock.instrument.quote, Asset::USD);
        assert_eq!(stock.instrument.exchange, Exchange::NASDAQ);
    }

    #[test]
    fn parse_invalid() {
        let result = "INVALID".parse::<Stock>();
        assert!(matches!(
            result,
            Err(StockParseError::InvalidInstrument(_))
        ));
    }

    // endregion

    // region: Display / round-trip

    #[test]
    fn display_format() {
        let stock: Stock = "AAPL/USD@NASDAQ".parse().unwrap();
        assert_eq!(stock.to_string(), "AAPL/USD@NASDAQ");
    }

    #[test]
    fn roundtrip() {
        let original: Stock = "AAPL/USD@NASDAQ".parse().unwrap();
        let displayed = original.to_string();
        let parsed: Stock = displayed.parse().unwrap();
        assert_eq!(original, parsed);
    }

    // endregion

    // region: const construction

    #[test]
    fn const_construction() {
        const STOCK: Stock =
            Stock::new(Instrument::new(Asset::BTC, Asset::USDT, Exchange::BINANCE));
        assert_eq!(STOCK.instrument.base, Asset::BTC);
    }

    // endregion

    // region: equality and hashing

    #[test]
    fn equality() {
        let a: Stock = "BTC/USDT@BINANCE".parse().unwrap();
        let b: Stock = "BTC/USDT@BINANCE".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn inequality() {
        let a: Stock = "BTC/USDT@BINANCE".parse().unwrap();
        let b: Stock = "ETH/USDT@BINANCE".parse().unwrap();
        assert_ne!(a, b);
    }

    #[test]
    fn usable_as_hashmap_key() {
        use std::collections::HashMap;
        let mut map: HashMap<Stock, f64> = HashMap::new();
        let stock: Stock = "AAPL/USD@NASDAQ".parse().unwrap();
        map.insert(stock, 150.0);
        let stock2: Stock = "AAPL/USD@NASDAQ".parse().unwrap();
        assert_eq!(map[&stock2], 150.0);
    }

    // endregion

    // region: TradeInstrument

    #[test]
    fn trade_instrument_trait() {
        let stock: Stock = "BTC/USDT@BINANCE".parse().unwrap();
        assert_eq!(stock.base().code(), "BTC");
        assert_eq!(stock.quote().code(), "USDT");
        assert_eq!(stock.exchange().code(), "BINANCE");
    }

    // endregion
}
