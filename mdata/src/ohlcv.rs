//! [`Ohlcv`]: a plain candle, raw straightforward implementation to reuse in code here and there.

use jiff::Timestamp;
use tradeprim::{price::Price, volume::Volume};

use crate::{Candle, HasLastPrice, HasTimestamp, HasVolume};

/// A candle: open, high, low, close and volume over an interval starting at `ts`.
///
/// Nothing is checked: a `low` above the `open` is stored as given.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ohlcv {
    ts: Timestamp,
    open: Price,
    high: Price,
    low: Price,
    close: Price,
    volume: Volume,
}

impl Ohlcv {
    pub fn new(
        ts: Timestamp,
        open: Price,
        high: Price,
        low: Price,
        close: Price,
        volume: Volume,
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

    /// Starts a candle for the interval starting at `ts` from its first record.
    pub fn seed<C: Candle + HasVolume>(ts: Timestamp, first: &C) -> Self {
        Self::new(
            ts,
            first.open(),
            first.high(),
            first.low(),
            first.close(),
            first.volume(),
        )
    }

    /// Grows the candle by a later record: the highest high, the lowest low, the record's close,
    /// the volumes added. The open and `ts` stay.
    ///
    /// Records must come in time order and belong to this candle's interval. `merge` checks
    /// neither: deciding which records make a candle is the aggregator's job.
    pub fn merge<C: Candle + HasVolume>(&mut self, next: &C) {
        self.high = self.high.max(next.high());
        self.low = self.low.min(next.low());
        self.close = next.close();
        self.volume += next.volume();
    }
}

impl HasTimestamp for Ohlcv {
    fn timestamp(&self) -> Timestamp {
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
}

impl HasVolume for Ohlcv {
    fn volume(&self) -> Volume {
        self.volume
    }
}

#[cfg(test)]
mod tests;
