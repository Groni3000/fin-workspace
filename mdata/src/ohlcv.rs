//! [`Ohlcv`]: a plain candle, raw straightforward implementation to reuse in code here and there.

use chrono::{DateTime, Utc};
use tradeprim::price::Price;

use crate::{Candle, HasLastPrice, HasTimestamp};

/// A candle: open, high, low, close and volume over an interval starting at `ts`.
///
/// Nothing is checked: a `low` above the `open` is stored as given.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ohlcv {
    ts: DateTime<Utc>,
    open: Price,
    high: Price,
    low: Price,
    close: Price,
    volume: u64,
}

impl Ohlcv {
    pub fn new(
        ts: DateTime<Utc>,
        open: Price,
        high: Price,
        low: Price,
        close: Price,
        volume: u64,
    ) -> Self {
        Self {
            ts,
            open,
            high,
            low,
            close,
            volume,
        }
    }
}

impl HasTimestamp for Ohlcv {
    fn timestamp(&self) -> DateTime<Utc> {
        self.ts
    }
}

/// The close: the latest price the candle knows.
impl HasLastPrice for Ohlcv {
    fn last_price(&self) -> Price {
        self.close
    }
}

impl Candle for Ohlcv {
    fn open(&self) -> Price {
        self.open
    }
    fn high(&self) -> Price {
        self.high
    }
    fn low(&self) -> Price {
        self.low
    }
    fn close(&self) -> Price {
        self.close
    }
    fn volume(&self) -> u64 {
        self.volume
    }
}
