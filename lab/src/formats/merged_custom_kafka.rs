use crate::formats::de_price_f64;
use jiff::Timestamp;
use mdata::{Candle, HasLastPrice, HasSymbol, HasTimestamp, HasVolume};
use serde::Deserialize;
use tradeprim::{price::Price, volume::Volume};

/// Custom candle used in internal kafka producer for topics like:
/// `md.db.GLBX.MDP3.<BASE_NAME>.FUT.merged.ohlcv-1s`
#[derive(Debug, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct MergedCandle {
    #[serde(with = "jiff::fmt::serde::timestamp::nanosecond::required")]
    ts_event: Timestamp,
    symbol: String,
    #[serde(deserialize_with = "de_price_f64")]
    open: Price,
    #[serde(deserialize_with = "de_price_f64")]
    high: Price,
    #[serde(deserialize_with = "de_price_f64")]
    low: Price,
    #[serde(deserialize_with = "de_price_f64")]
    close: Price,
    volume: u64,
    #[serde(with = "jiff::fmt::serde::timestamp::nanosecond::required")]
    ts_ingest: Timestamp,
}

impl HasTimestamp for MergedCandle {
    fn timestamp(&self) -> Timestamp {
        self.ts_event
    }
}

impl HasSymbol for MergedCandle {
    fn symbol(&self) -> &str {
        &self.symbol
    }
}

impl HasLastPrice for MergedCandle {
    fn last_price(&self) -> Price {
        self.close
    }
}

impl Candle for MergedCandle {
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

/// The source reports whole contracts.
impl HasVolume for MergedCandle {
    fn volume(&self) -> Volume {
        Volume::from_units(self.volume)
    }
}
