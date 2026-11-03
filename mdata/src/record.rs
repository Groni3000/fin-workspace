//! Capabilities of a single market-data record.
//!
//! Each trait names one thing a record can tell you. Code that consumes market
//! data asks for the narrowest set it needs (`Candle + Instrumented` for a
//! simulated executor, `RelevantPrice` for a mark-to-market), so any format
//! that provides those capabilities plugs in.

use chrono::{DateTime, Utc};
use instrid::instruments::Instrument;
use tradeprim::price::Price;

/// The record happened at a known point in time.
pub trait Timestamped {
    fn timestamp(&self) -> DateTime<Utc>;
}

/// The record belongs to a known internal representation of an instrument.
pub trait Instrumented {
    fn instrument(&self) -> Instrument;
}

/// The record carries a venue/vendor symbol (e.g. a Globex code) that still
/// has to be resolved into an [`Instrument`].
pub trait Symboled {
    fn symbol(&self) -> &str;
}

/// A trait for data that have as little useful data
/// as possible: when and what the price was at that time.
pub trait RelevantPrice: Timestamped {
    fn last_price(&self) -> Price;
}

/// Represents an unknown time span aggregated candle.
///
/// Naturally extends RelevantPrice.
pub trait Candle: RelevantPrice {
    fn open(&self) -> Price;
    fn high(&self) -> Price;
    fn low(&self) -> Price;
    fn close(&self) -> Price;
    fn volume(&self) -> u64;
}
