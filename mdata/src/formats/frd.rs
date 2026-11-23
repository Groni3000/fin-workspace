//! FRD one-minute files: one candle per line, `YYYY-MM-DD HH:MM:SS,open,high,low,close,volume`,
//! the time in US/Eastern (exchange time), the volume in whole contracts. Parsed into [`Ohlcv`].
//!
//! [`parse_line`] parses one line. With the `frd-chain` feature, `ChainReader` reads a futures
//! chain's files as one stream.

#[cfg(feature = "frd-chain")]
mod chain;
#[cfg(feature = "frd-chain")]
pub use chain::{ChainReader, ReadError};

use std::{fmt::Display, num::ParseIntError, str::FromStr, sync::LazyLock};

use crate::Ohlcv;
use jiff::{
    Timestamp,
    civil::DateTime,
    tz::{AmbiguousOffset, TimeZone},
};
use tradeprim::{decimal::ParseDecimalError, price::Price, volume::Volume};

/// The exchange's time zone, which FRD times are in.
pub static EXCHANGE_TZ: LazyLock<TimeZone> = LazyLock::new(|| {
    TimeZone::get("America/New_York").expect("the tz database has America/New_York")
});

#[derive(Debug, Clone, PartialEq)]
pub enum Field {
    Timestamp,
    Price,
    Volume,
}

#[derive(Debug)]
pub enum ParseError {
    Missing(Field),
    TimezoneConversionError(String),
    BadTimestamp(String),
    PriceParsingError(ParseDecimalError),
    VolumeParsingError(ParseIntError),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::Missing(field) => write!(f, "Missing field: {:?}", field),
            ParseError::PriceParsingError(err) => err.fmt(f),
            ParseError::TimezoneConversionError(err) => err.fmt(f),
            ParseError::BadTimestamp(err) => err.fmt(f),
            ParseError::VolumeParsingError(err) => err.fmt(f),
        }
    }
}

/// Parses one line of an FRD file.
pub fn parse_line(s: &str) -> Result<Ohlcv, ParseError> {
    let mut split = s.trim().split(',');

    let raw_ts = split.next().ok_or(ParseError::Missing(Field::Timestamp))?;
    let ts = to_utc(raw_ts, &EXCHANGE_TZ)?;
    let mut price = || -> Result<Price, ParseError> {
        let field = split.next().ok_or(ParseError::Missing(Field::Price))?;
        Price::from_str(field).map_err(ParseError::PriceParsingError)
    };
    let (open, high, low, close) = (price()?, price()?, price()?, price()?);
    let volume: u64 = split
        .next()
        .ok_or(ParseError::Missing(Field::Volume))?
        .parse()
        .map_err(ParseError::VolumeParsingError)?;

    Ok(Ohlcv::new(
        ts,
        open,
        high,
        low,
        close,
        Volume::from_units(volume),
    ))
}

/// Exchange time to UTC. An ambiguous time (the hour repeated when DST ends) takes the first.
/// A skipped time (DST starts) is a [`ParseError::TimezoneConversionError`]; a time outside
/// jiff's range (the very end of year 9999) is a [`ParseError::BadTimestamp`].
fn to_utc(raw_ts: &str, tz: &TimeZone) -> Result<Timestamp, ParseError> {
    let local =
        parse_civil(raw_ts).ok_or_else(|| ParseError::BadTimestamp(format!("{:?}", raw_ts)))?;
    let ts = tz.to_ambiguous_timestamp(local);
    let nonexistent = || {
        ParseError::TimezoneConversionError(format!(
            "Non existent local time {:?} for timezone {}",
            raw_ts,
            tz.iana_name().unwrap_or("?")
        ))
    };
    match ts.offset() {
        AmbiguousOffset::Gap { .. } => Err(nonexistent()),
        AmbiguousOffset::Unambiguous { .. } | AmbiguousOffset::Fold { .. } => ts
            .earlier()
            .map_err(|_| ParseError::BadTimestamp(format!("{:?} is out of range", raw_ts))),
    }
}

/// `YYYY-MM-DD HH:MM:SS`, checking only the length and that digits are where they should be.
fn parse_civil(raw_ts: &str) -> Option<DateTime> {
    let bytes = raw_ts.as_bytes();
    if bytes.len() != 19 {
        return None;
    }

    #[inline(always)]
    fn d2(b: &[u8], i: usize) -> Option<i8> {
        if b[i].is_ascii_digit() && b[i + 1].is_ascii_digit() {
            return Some((b[i] - b'0') as i8 * 10 + (b[i + 1] - b'0') as i8);
        }
        None
    }

    let year = i16::from(d2(bytes, 0)?) * 100 + i16::from(d2(bytes, 2)?); // "20","25" -> 2025
    let month = d2(bytes, 5)?;
    let day = d2(bytes, 8)?;
    let hour = d2(bytes, 11)?;
    let min = d2(bytes, 14)?;
    let sec = d2(bytes, 17)?;

    DateTime::new(year, month, day, hour, min, sec, 0).ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skipped_time_is_a_timezone_error() {
        let err = parse_line("2025-03-09 02:30:00,1,1,1,1,1").unwrap_err();
        assert!(
            matches!(err, ParseError::TimezoneConversionError(_)),
            "{err:?}"
        );
    }

    #[test]
    fn time_past_the_supported_range_is_a_bad_timestamp() {
        let err = parse_line("9999-12-31 23:59:59,1,1,1,1,1").unwrap_err();
        assert!(matches!(err, ParseError::BadTimestamp(_)), "{err:?}");
    }
}
