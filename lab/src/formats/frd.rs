use chrono_tz::{Tz, US::Eastern as ExchangeTZ};
use std::{fmt::Display, num::ParseIntError, str::FromStr};

use chrono::{DateTime, NaiveDate, NaiveDateTime, TimeZone, Utc};
use serde::{Deserialize, Serialize};
use tradeprim::price::{ParsePriceError, Price};

use crate::market_data::{Candle, RelevantPrice, Timestamped};

#[derive(Serialize, Deserialize)]
pub struct RawFrdCandle<'a> {
    timestamp: NaiveDateTime,
    high: &'a str,
    low: &'a str,
    open: &'a str,
    close: &'a str,
    volume: &'a str,
}

#[derive(Deserialize, Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
#[serde(try_from = "RawFrdCandle")]
pub struct FrdCandle {
    timestamp: DateTime<Utc>,
    high: Price,
    low: Price,
    open: Price,
    close: Price,
    volume: u64,
}

impl Timestamped for FrdCandle {
    fn timestamp(&self) -> DateTime<Utc> {
        self.timestamp
    }
}

impl RelevantPrice for FrdCandle {
    fn last_price(&self) -> Price {
        self.close
    }
}

impl Candle for FrdCandle {
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

#[derive(Debug, Clone, PartialEq)]
pub enum FrdField {
    Timestamp,
    Price,
    Volume,
}

#[derive(Debug)]
pub enum FrdCandleParsingError {
    Missing(FrdField),
    TimezoneConversionError(String),
    BadTimestamp(String),
    PriceParsingError(ParsePriceError),
    VolumeParsingError(ParseIntError),
}

impl Display for FrdCandleParsingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FrdCandleParsingError::Missing(field) => write!(f, "Missing field: {:?}", field),
            FrdCandleParsingError::PriceParsingError(err) => err.fmt(f),
            FrdCandleParsingError::TimezoneConversionError(err) => err.fmt(f),
            FrdCandleParsingError::BadTimestamp(err) => err.fmt(f),
            FrdCandleParsingError::VolumeParsingError(err) => err.fmt(f),
        }
    }
}

impl<'a> TryFrom<RawFrdCandle<'a>> for FrdCandle {
    type Error = FrdCandleParsingError;

    fn try_from(value: RawFrdCandle) -> Result<Self, Self::Error> {
        // Ambiguous => choose first
        let utc_converted = match ExchangeTZ.from_local_datetime(&value.timestamp) {
            chrono::LocalResult::Single(ts) => ts.with_timezone(&Utc),
            chrono::LocalResult::Ambiguous(a, _) => a.with_timezone(&Utc),
            chrono::LocalResult::None => {
                return Err(FrdCandleParsingError::TimezoneConversionError(format!(
                    "Non existent local time {:?} for timezone {:?}",
                    value.timestamp, ExchangeTZ
                )));
            }
        };

        let open = Price::from_str(value.open).map_err(FrdCandleParsingError::PriceParsingError)?;
        let close =
            Price::from_str(value.close).map_err(FrdCandleParsingError::PriceParsingError)?;
        let high = Price::from_str(value.high).map_err(FrdCandleParsingError::PriceParsingError)?;
        let low = Price::from_str(value.low).map_err(FrdCandleParsingError::PriceParsingError)?;
        let volume: u64 = value
            .volume
            .parse()
            .map_err(FrdCandleParsingError::VolumeParsingError)?;

        Ok(FrdCandle::new(
            utc_converted,
            high,
            low,
            open,
            close,
            volume,
        ))
    }
}

impl FrdCandle {
    pub fn new(
        timestamp: DateTime<Utc>,
        high: Price,
        low: Price,
        open: Price,
        close: Price,
        volume: u64,
    ) -> Self {
        Self {
            timestamp,
            high,
            low,
            open,
            close,
            volume,
        }
    }

    #[allow(dead_code)]
    /// General function. Pretty much slow because of
    /// the naive datetime parsing.
    ///
    fn convert_str_with_tz_to_utc_timestamp(
        raw_ts: &str,
        tz: Tz,
    ) -> Result<DateTime<Utc>, FrdCandleParsingError> {
        let naive_ts = chrono::NaiveDateTime::parse_from_str(raw_ts, "%Y-%m-%d %H:%M:%S")
            .map_err(|err| FrdCandleParsingError::TimezoneConversionError(err.to_string()))?;
        // Ambiguous => choose first
        let utc_converted = match tz.from_local_datetime(&naive_ts) {
            chrono::LocalResult::Single(ts) => ts.with_timezone(&Utc),
            chrono::LocalResult::Ambiguous(a, _) => a.with_timezone(&Utc),
            chrono::LocalResult::None => {
                return Err(FrdCandleParsingError::TimezoneConversionError(format!(
                    "Non existent local time {:?} for timezone {:?}",
                    raw_ts, tz
                )));
            }
        };

        Ok(utc_converted)
    }

    fn frd_convert_str_with_tz_to_utc_timestamp(
        raw_ts: &str,
        tz: Tz,
    ) -> Result<DateTime<Utc>, FrdCandleParsingError> {
        let naive_ts = Self::frd_ts_parser(raw_ts)
            .ok_or_else(|| FrdCandleParsingError::BadTimestamp(format!("{:?}", raw_ts)))?;
        // Ambiguous => choose first
        let utc_converted = match tz.from_local_datetime(&naive_ts) {
            chrono::LocalResult::Single(ts) => ts.with_timezone(&Utc),
            chrono::LocalResult::Ambiguous(a, _) => a.with_timezone(&Utc),
            chrono::LocalResult::None => {
                return Err(FrdCandleParsingError::TimezoneConversionError(format!(
                    "Non existent local time {:?} for timezone {:?}",
                    raw_ts, tz
                )));
            }
        };

        Ok(utc_converted)
    }

    // Just a helper function with minimal validation
    // (len + digits in correct spots)
    fn frd_ts_parser(raw_ts: &str) -> Option<NaiveDateTime> {
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

    pub fn from_frd_csv_line(s: &str) -> Result<Self, FrdCandleParsingError> {
        let mut split = s.trim().split(',');

        let raw_ts = split
            .next()
            .ok_or(FrdCandleParsingError::Missing(FrdField::Timestamp))?;
        let utc_ts = Self::frd_convert_str_with_tz_to_utc_timestamp(raw_ts, ExchangeTZ)?;
        let high = Price::from_str(
            split
                .next()
                .ok_or(FrdCandleParsingError::Missing(FrdField::Price))?,
        )
        .map_err(FrdCandleParsingError::PriceParsingError)?;
        let low = Price::from_str(
            split
                .next()
                .ok_or(FrdCandleParsingError::Missing(FrdField::Price))?,
        )
        .map_err(FrdCandleParsingError::PriceParsingError)?;
        let open = Price::from_str(
            split
                .next()
                .ok_or(FrdCandleParsingError::Missing(FrdField::Price))?,
        )
        .map_err(FrdCandleParsingError::PriceParsingError)?;
        let close = Price::from_str(
            split
                .next()
                .ok_or(FrdCandleParsingError::Missing(FrdField::Price))?,
        )
        .map_err(FrdCandleParsingError::PriceParsingError)?;
        let volume: u64 = split
            .next()
            .ok_or(FrdCandleParsingError::Missing(FrdField::Volume))?
            .parse()
            .map_err(FrdCandleParsingError::VolumeParsingError)?;

        Ok(FrdCandle::new(utc_ts, high, low, open, close, volume))
    }

    pub fn timestamp(&self) -> DateTime<Utc> {
        self.timestamp
    }

    pub fn high(&self) -> Price {
        self.high
    }

    pub fn low(&self) -> Price {
        self.low
    }

    pub fn open(&self) -> Price {
        self.open
    }

    pub fn close(&self) -> Price {
        self.close
    }

    pub fn volume(&self) -> u64 {
        self.volume
    }
}
