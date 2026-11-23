//! FRD one-minute files: one candle per line, `YYYY-MM-DD HH:MM:SS,open,high,low,close,volume`,
//! the time in US/Eastern (exchange time), the volume in whole contracts. Parsed into [`Ohlcv`].
//!
//! [`parse_line`] parses one line; [`ChainReader`] reads a futures chain's files as one stream.

mod chain;
pub use chain::{ChainReader, ReadError};

use chrono_tz::{Tz, US::Eastern as ExchangeTZ};
use std::{fmt::Display, num::ParseIntError, str::FromStr};

use chrono::{DateTime, NaiveDate, NaiveDateTime, TimeZone, Utc};
use mdata::Ohlcv;

use crate::time_bridge::to_jiff;
use tradeprim::{decimal::ParseDecimalError, price::Price, volume::Volume};

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
    let ts = to_utc(raw_ts, ExchangeTZ)?;
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
        to_jiff(ts),
        open,
        high,
        low,
        close,
        Volume::from_units(volume),
    ))
}

/// Exchange time to UTC. An ambiguous time (the hour repeated when DST ends) takes the first.
fn to_utc(raw_ts: &str, tz: Tz) -> Result<DateTime<Utc>, ParseError> {
    let naive_ts =
        parse_naive(raw_ts).ok_or_else(|| ParseError::BadTimestamp(format!("{:?}", raw_ts)))?;
    match tz.from_local_datetime(&naive_ts) {
        chrono::LocalResult::Single(ts) => Ok(ts.with_timezone(&Utc)),
        chrono::LocalResult::Ambiguous(a, _) => Ok(a.with_timezone(&Utc)),
        chrono::LocalResult::None => Err(ParseError::TimezoneConversionError(format!(
            "Non existent local time {:?} for timezone {:?}",
            raw_ts, tz
        ))),
    }
}

/// `YYYY-MM-DD HH:MM:SS`, checking only the length and that digits are where they should be.
fn parse_naive(raw_ts: &str) -> Option<NaiveDateTime> {
    let bytes = raw_ts.as_bytes();
    if bytes.len() != 19 {
        return None;
    }

    #[inline(always)]
    fn d2(b: &[u8], i: usize) -> Option<u32> {
        if b[i].is_ascii_digit() && b[i + 1].is_ascii_digit() {
            return Some((b[i] - b'0') as u32 * 10 + (b[i + 1] - b'0') as u32);
        }
        None
    }

    let year = d2(bytes, 0)? * 100 + d2(bytes, 2)?; // "20","25" -> 2025
    let month = d2(bytes, 5)?;
    let day = d2(bytes, 8)?;
    let hour = d2(bytes, 11)?;
    let min = d2(bytes, 14)?;
    let sec = d2(bytes, 17)?;

    NaiveDate::from_ymd_opt(year as i32, month, day)?.and_hms_opt(hour, min, sec)
}
