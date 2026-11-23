//! Capabilities of a single market-data record.
//!
//! Each trait names one thing a record can tell you. Code that consumes market
//! data asks for the narrowest set it needs (`Candle + HasInstrument` for a
//! simulated executor, `HasLastPrice` for a mark-to-market), so any format
//! that provides those capabilities plugs in.

use instrid::instruments::Instrument;
use jiff::Timestamp;
use tradeprim::{price::Price, volume::Volume};

/// The record happened at a known point in time.
pub trait HasTimestamp {
    fn timestamp(&self) -> Timestamp;
}

/// The record belongs to a known internal representation of an instrument.
pub trait HasInstrument {
    fn instrument(&self) -> Instrument;
}

/// The record carries a venue/vendor symbol (e.g. a Globex code) that still
/// has to be resolved into an [`Instrument`].
pub trait HasSymbol {
    fn symbol(&self) -> &str;
}

/// A trait for data that have as little useful data
/// as possible: when and what the price was at that time.
pub trait HasLastPrice: HasTimestamp {
    fn last_price(&self) -> Price;
}

/// Represents an unknown time span aggregated candle.
///
/// Naturally extends HasLastPrice.
pub trait Candle: HasLastPrice {
    fn open(&self) -> Price;
    fn high(&self) -> Price;
    fn low(&self) -> Price;
    fn close(&self) -> Price;
}

/// The record knows how much traded. Not part of [`Candle`]: some sources may not have volume,
/// and a made-up zero would mislead whoever reads it.
pub trait HasVolume {
    fn volume(&self) -> Volume;
}
