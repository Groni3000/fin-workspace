use crate::formats::de_price_f64;
use crate::market_data::{Candle, RelevantPrice, Symboled, Timestamped};
use chrono::serde::ts_nanoseconds;
use chrono::{DateTime, Utc};
use serde::Deserialize;
use tradeprim::price::Price;

/// Custom candle used in internal kafka producer for topics like:
/// `md.db.GLBX.MDP3.<BASE_NAME>.FUT.merged.ohlcv-1s`
#[derive(Debug, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub struct MergedCandle {
    #[serde(with = "ts_nanoseconds")]
    ts_event: DateTime<Utc>,
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
    #[serde(with = "ts_nanoseconds")]
    ts_ingest: DateTime<Utc>,
}

impl Timestamped for MergedCandle {
    fn timestamp(&self) -> DateTime<Utc> {
        self.ts_event
    }
}

impl Symboled for MergedCandle {
    fn symbol(&self) -> &str {
        &self.symbol
    }
}

impl RelevantPrice for MergedCandle {
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

    fn volume(&self) -> u64 {
        self.volume
    }
}
