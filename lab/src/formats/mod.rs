use chrono::{DateTime, Utc};
use instrid::instruments::Instrument;
use tradeprim::price::Price;

use crate::market_data::{Candle, Instrumented, RelevantPrice, Timestamped};

pub mod custom;
pub mod frd;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tagged<R> {
    instrument: Instrument,
    record: R,
}

impl<R> Tagged<R> {
    pub fn new(instrument: Instrument, record: R) -> Self {
        Self { instrument, record }
    }
}

impl<R: Timestamped> Timestamped for Tagged<R> {
    fn timestamp(&self) -> DateTime<Utc> {
        self.record.timestamp()
    }
}
impl<R: RelevantPrice> RelevantPrice for Tagged<R> {
    fn last_price(&self) -> Price {
        self.record.last_price()
    }
}
impl<R: Candle> Candle for Tagged<R> {
    fn open(&self) -> Price {
        self.record.open()
    }
    fn high(&self) -> Price {
        self.record.high()
    }
    fn low(&self) -> Price {
        self.record.low()
    }
    fn close(&self) -> Price {
        self.record.close()
    }
    fn volume(&self) -> u64 {
        self.record.volume()
    }
}
impl<R> Instrumented for Tagged<R> {
    fn instrument(&self) -> Instrument {
        self.instrument
    }
}
