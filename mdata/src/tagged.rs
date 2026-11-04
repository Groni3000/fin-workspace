//! Attaching an instrument to a record that doesn't carry one.

use chrono::{DateTime, Utc};
use instrid::instruments::Instrument;
use tradeprim::price::Price;

use crate::record::{Candle, Instrumented, RelevantPrice, Timestamped};

/// A record paired with the instrument it belongs to.
///
/// Most file and wire formats identify the instrument once (file name, topic,
/// symbol), not per record. `Tagged` resolves that once at the reader and
/// makes the record [`Instrumented`], while forwarding every other capability
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

#[cfg(test)]
mod tests {
    use instrid::{
        asset::{Asset, AssetClass},
        instruments::Stock,
        mic::Mic,
    };
    use tradeprim::currency::Currency;

    use super::*;

    #[derive(Debug, Clone, Copy)]
    struct Bar {
        ts: DateTime<Utc>,
        o: Price,
        h: Price,
        l: Price,
        c: Price,
        /// Distinct from `c`: a `last_price` wired to `close()` must not pass.
        last: Price,
        v: u64,
    }

    impl Timestamped for Bar {
        fn timestamp(&self) -> DateTime<Utc> {
            self.ts
        }
    }
    impl RelevantPrice for Bar {
        fn last_price(&self) -> Price {
            self.last
        }
    }
    impl Candle for Bar {
        fn open(&self) -> Price {
            self.o
        }
        fn high(&self) -> Price {
            self.h
        }
        fn low(&self) -> Price {
            self.l
        }
        fn close(&self) -> Price {
            self.c
        }
        fn volume(&self) -> u64 {
            self.v
        }
    }

    fn spy() -> Instrument {
        Instrument::Stock(Stock::new(
            Asset::new("SPY", AssetClass::Equity).unwrap(),
            Asset::new("USD", AssetClass::Currency).unwrap(),
            Mic::arcx(),
            Currency::usd(),
        ))
    }

    #[test]
    fn forwards_every_capability_and_adds_the_instrument() {
        let bar = Bar {
            ts: DateTime::from_timestamp_nanos(1_700_000_000_000_000_000),
            o: Price::from_str_unchecked("1"),
            h: Price::from_str_unchecked("4"),
            l: Price::from_str_unchecked("0.5"),
            c: Price::from_str_unchecked("2"),
            last: Price::from_str_unchecked("3"),
            v: 7,
        };
        let tagged = Tagged::new(spy(), bar);

        assert_eq!(tagged.instrument(), spy());
        assert_eq!(tagged.timestamp(), bar.ts);
        assert_eq!(tagged.last_price(), bar.last);
        assert_eq!(tagged.open(), bar.o);
        assert_eq!(tagged.high(), bar.h);
        assert_eq!(tagged.low(), bar.l);
        assert_eq!(tagged.close(), bar.c);
        assert_eq!(tagged.volume(), bar.v);
    }
}
