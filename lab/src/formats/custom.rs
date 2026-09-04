use chrono::{DateTime, Utc, serde::ts_nanoseconds};
use foldhash::HashMap;
use instrid::instruments::Instrument;
use serde::Deserialize;
use serde::de::DeserializeOwned;

use crate::formats::de_price_f64;
use tradeprim::price::Price;

use crate::market_data::{Candle, RelevantPrice, Timestamped};
use crate::{formats::Tagged, market_data::Symboled};

use std::{
    fmt::Display,
    marker::PhantomData,
    str::Utf8Error,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use rdkafka::{
    ClientConfig, Message,
    consumer::{BaseConsumer, Consumer},
    error::KafkaError,
    util::Timeout,
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
        Some(self.cmp(other))
    }
}

/// Ordered by `ts_event`, then by the remaining `Eq` fields so that `cmp() == Equal`
/// implies `==`. One topic carries every symbol, so equal timestamps are the norm.
impl Ord for CustomDatabentoAggregatedCandle {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (
            self.ts_event,
            &self.symbol,
            self.instrument_id,
            self.publisher_id,
            &self.src,
        )
            .cmp(&(
                other.ts_event,
                &other.symbol,
                other.instrument_id,
                other.publisher_id,
                &other.src,
            ))
    }
}

impl Timestamped for CustomDatabentoAggregatedCandle {
    fn timestamp(&self) -> DateTime<Utc> {
        self.ts_event
    }
}

impl Symboled for CustomDatabentoAggregatedCandle {
    fn symbol(&self) -> &str {
        &self.symbol
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
pub struct CustomDatabentoConsumerMd<T> {
    consumer: BaseConsumer,
    /// Set from a Ctrl-C handler; ends iteration so the consumer drops
    /// (and librdkafka leaves the group cleanly).
    shutdown: Arc<AtomicBool>,
    symbols: HashMap<String, Instrument>,
    high_watermark: i64,
    _record: PhantomData<fn() -> T>,
}

#[cfg(feature = "kafka")]
impl<T> CustomDatabentoConsumerMd<T> {
    #[expect(clippy::too_many_arguments, reason = "Kafka has too many setting.")]
    pub fn new(
        bootstrap_servers: &str,
        group_id: &str,
        auto_offset_reset: &str,
        enable_auto_commit: bool,
        topic: &str,
        shutdown: Arc<AtomicBool>,
        symbols: HashMap<String, Instrument>,
        settings: KafkaSettings,
    ) -> Self {
        let consumer: BaseConsumer = ClientConfig::new()
            .set("bootstrap.servers", bootstrap_servers)
            .set("group.id", group_id)
            .set("auto.offset.reset", auto_offset_reset)
            .set("enable.auto.commit", enable_auto_commit.to_string())
            .set("fetch.min.bytes", settings.min_bytes.to_string())
            .set("fetch.wait.max.ms", settings.wait_max_ms.to_string())
            .set("queued.min.messages", settings.min_messages.to_string())
            .set(
                "queued.max.messages.kbytes",
                settings.max_messages_kbytes.to_string(),
            )
            .create()
            .expect("failed to create consumer");

        consumer
            .subscribe(&[topic])
            .expect("failed to subscribe to topic");

        let (_low, high) = consumer
            .fetch_watermarks(topic, 0, Timeout::After(Duration::from_secs(10)))
            .expect("Coudn't get (low, high) watermarks");

        Self {
            consumer,
            shutdown,
            symbols,
            high_watermark: high,
            _record: PhantomData,
        }
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

#[cfg(feature = "kafka")]
impl Display for KafkaMdError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[cfg(feature = "kafka")]
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
impl<T: DeserializeOwned + Symboled> Iterator for CustomDatabentoConsumerMd<T> {
    type Item = Result<Tagged<T>, KafkaMdError>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.shutdown.load(Ordering::Relaxed) {
                return None;
            }
            match self.consumer.poll(Duration::from_millis(500)) {
                Some(Ok(msg)) => {
                    // `>=`, not `==`: a control record or a gap at that exact offset
                    // would otherwise never match and the replay would poll forever.
                    if msg.offset() >= self.high_watermark - 1 {
                        return None;
                    };
                    let record = match msg.payload_view::<str>() {
                        Some(Ok(payload)) => payload,
                        Some(Err(e)) => return Some(Err(KafkaMdError::Utf8Error(e))),
                        None => return Some(Err(KafkaMdError::EmptyPayload)),
                    };

                    return match serde_json::from_str::<T>(record) {
                        Ok(candle) => {
                            let Some(&instrument) = self.symbols.get(candle.symbol()) else {
                                continue; // not ours: spreads, other products, other months
                            };
                            Some(Ok(Tagged::new(instrument, candle)))
                        }
                        Err(e) => Some(Err(KafkaMdError::Json(e))),
                    };
                }
                Some(Err(e)) => return Some(Err(KafkaMdError::Kafka(e))),
                None => continue,
            }
        }
    }
}

pub struct KafkaSettings {
    min_bytes: u32,
    wait_max_ms: u32,
    min_messages: u32,
    max_messages_kbytes: u32,
}

impl KafkaSettings {
    pub fn new(
        min_bytes: u32,
        wait_max_ms: u32,
        min_messages: u32,
        max_messages_kbytes: u32,
    ) -> Self {
        Self {
            min_bytes,
            wait_max_ms,
            min_messages,
            max_messages_kbytes,
        }
    }

    pub fn min_bytes(&self) -> u32 {
        self.min_bytes
    }

    pub fn wait_max_ms(&self) -> u32 {
        self.wait_max_ms
    }

    pub fn min_messages(&self) -> u32 {
        self.min_messages
    }

    pub fn max_messages_kbytes(&self) -> u32 {
        self.max_messages_kbytes
    }

    /// Bulk replay: big batches, latency irrelevant.
    pub fn replay() -> Self {
        // 1^10 = 1 KiB
        // 1^20 = 1 MiB
        // 1^30 = 1 GiB
        Self::new(1 << 20, 500, 1_000_000, 1 << 20)
    }
    /// Live: reply immediately.
    ///
    /// Something like this:
    /// - min_bytes = 1
    /// - wait_max_ms = 500
    /// - queued_min_msgs = 100_000
    /// - queued_max_msgs_kbytes = 65_536 (64 MiB)
    pub fn live() -> Self {
        Self::new(1, 10, 100_000, 65_536)
    }
}

impl Default for KafkaSettings {
    fn default() -> Self {
        Self::live()
    }
}
