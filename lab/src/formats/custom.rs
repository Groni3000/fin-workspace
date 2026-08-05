use chrono::{DateTime, Utc, serde::ts_nanoseconds};
use serde::{Deserialize, Deserializer};
use tradeprim::price::Price;

use crate::market_data::{Candle, RelevantPrice, Timestamped};

use std::fmt::Display;
#[cfg(feature = "kafka")]
use std::{str::Utf8Error, time::Duration};

#[cfg(feature = "kafka")]
use rdkafka::{
    ClientConfig, Message,
    consumer::{BaseConsumer, Consumer},
    error::KafkaError,
};

// #[cfg(feature = "kafka")]
// use crate::market_data::MarketData;

// --------------
// --- Record ---
// --------------

// Format:
// {
// "symbol": "CLZ6-CLM7", "dataset": "GLBX.MDP3",
// "schema": "ohlcv-1s", "instrument_id": 182572,
// "publisher_id": 1,
// "ts_event": 1783000818000000000,
// "time": "2026-07-02T14:00:18+00:00",
// "src": "CL.FUT",
// "open": 0.92, "high": 0.92, "low": 0.92, "close": 0.92, "volume": 34}
#[derive(Debug, Deserialize)]
pub struct CustomDatabentoAggregatedCandle {
    pub symbol: String,
    // pub dataset: String,
    // pub schema: String,
    pub instrument_id: u64,
    pub publisher_id: u64,
    #[serde(with = "ts_nanoseconds")]
    pub ts_event: DateTime<Utc>,
    // pub time: String,
    pub src: String,
    #[serde(deserialize_with = "de_price_f64")]
    pub open: Price,
    #[serde(deserialize_with = "de_price_f64")]
    pub high: Price,
    #[serde(deserialize_with = "de_price_f64")]
    pub low: Price,
    #[serde(deserialize_with = "de_price_f64")]
    pub close: Price,
    pub volume: u64,
}

impl PartialEq for CustomDatabentoAggregatedCandle {
    fn eq(&self, other: &Self) -> bool {
        self.symbol == other.symbol
            && self.instrument_id == other.instrument_id
            && self.publisher_id == other.publisher_id
            && self.ts_event == other.ts_event
            && self.src == other.src
    }
}

impl Eq for CustomDatabentoAggregatedCandle {}

impl PartialOrd for CustomDatabentoAggregatedCandle {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.ts_event.partial_cmp(&other.ts_event)
    }
}

impl Ord for CustomDatabentoAggregatedCandle {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.ts_event.cmp(&other.ts_event)
    }
}

fn de_price_f64<'de, D: Deserializer<'de>>(d: D) -> Result<Price, D::Error> {
    let v = f64::deserialize(d)?;
    Price::try_from(v).map_err(serde::de::Error::custom)
}

impl Timestamped for CustomDatabentoAggregatedCandle {
    fn timestamp(&self) -> DateTime<Utc> {
        self.ts_event
    }
}

impl RelevantPrice for CustomDatabentoAggregatedCandle {
    fn last_price(&self) -> Price {
        self.close
    }
}

impl Candle for CustomDatabentoAggregatedCandle {
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

// -------------------
// --- Market Data ---
// -------------------
#[cfg(feature = "kafka")]
pub struct CustomDatabentoConsumerMd {
    consumer: BaseConsumer,
}

#[cfg(feature = "kafka")]
impl CustomDatabentoConsumerMd {
    pub fn new(
        bootstrap_servers: &str,
        group_id: &str,
        auto_offset_reset: &str,
        enable_auto_commit: bool,
        topic: &str,
    ) -> Self {
        let consumer: BaseConsumer = ClientConfig::new()
            .set("bootstrap.servers", bootstrap_servers)
            .set("group.id", group_id)
            .set("auto.offset.reset", auto_offset_reset)
            .set("enable.auto.commit", enable_auto_commit.to_string())
            .create()
            .expect("failed to create consumer");

        consumer
            .subscribe(&[topic])
            .expect("failed to subscribe to topic");

        Self { consumer }
    }

    pub fn consumer(&self) -> &BaseConsumer {
        &self.consumer
    }
}

#[cfg(feature = "kafka")]
#[derive(Debug)]
pub enum KafkaMdError {
    Kafka(KafkaError),
    EmptyPayload,
    Utf8Error(Utf8Error),
    Json(serde_json::Error),
}

impl Display for KafkaMdError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for KafkaMdError {}

#[cfg(feature = "kafka")]
impl From<serde_json::Error> for KafkaMdError {
    fn from(value: serde_json::Error) -> Self {
        KafkaMdError::Json(value)
    }
}

#[cfg(feature = "kafka")]
impl From<KafkaError> for KafkaMdError {
    fn from(value: KafkaError) -> Self {
        KafkaMdError::Kafka(value)
    }
}

#[cfg(feature = "kafka")]
impl Iterator for CustomDatabentoConsumerMd {
    type Item = Result<CustomDatabentoAggregatedCandle, KafkaMdError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.consumer.poll(Duration::from_millis(500)) {
                Some(Ok(msg)) => {
                    let record = match msg.payload_view::<str>()? {
                        Ok(payload) => payload,
                        Err(e) => return Some(Err(KafkaMdError::Utf8Error(e))),
                    };

                    match serde_json::from_str::<CustomDatabentoAggregatedCandle>(record) {
                        Ok(candle) => Some(Ok(candle)),
                        Err(e) => Some(Err(KafkaMdError::Json(e))),
                    }
                }
                Some(Err(e)) => return Some(Err(KafkaMdError::Kafka(e))),
                None => {
                    continue;
                }
            };
        }
    }
}
