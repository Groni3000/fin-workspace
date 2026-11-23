//! Attaching an instrument to a record that doesn't carry one.

use chrono::{DateTime, Utc};
use instrid::instruments::Instrument;
use tradeprim::{price::Price, volume::Volume};

use crate::record::{Candle, HasInstrument, HasLastPrice, HasTimestamp, HasVolume};

/// A record paired with the instrument it belongs to.
///
/// Most file and wire formats identify the instrument once (file name, topic,
/// symbol), not per record. `Tagged` resolves that once at the reader and
/// makes the record [`HasInstrument`], while forwarding every other capability
/// the inner record has.
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

impl<R: HasTimestamp> HasTimestamp for Tagged<R> {
    fn timestamp(&self) -> DateTime<Utc> {
        self.record.timestamp()
    }
}

impl<R: HasLastPrice> HasLastPrice for Tagged<R> {
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
}

impl<R: HasVolume> HasVolume for Tagged<R> {
    fn volume(&self) -> Volume {
        self.record.volume()
    }
}

impl<R> HasInstrument for Tagged<R> {
    fn instrument(&self) -> Instrument {
        self.instrument
    }
}
