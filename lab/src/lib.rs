use std::{
    fmt::{Display, Pointer},
    num::ParseIntError,
    str::FromStr,
};

use chrono::{DateTime, NaiveDateTime, TimeZone, Utc};
use chrono_tz::{Tz, US::Eastern as ExchangeTZ};
use serde::{Deserialize, Serialize};
use tradeprim::price::{ParsePriceError, Price};

#[derive(Serialize, Deserialize)]
pub struct RawFrdCandle<'a> {
    timestamp: NaiveDateTime,
    high: &'a str,
    low: &'a str,
    open: &'a str,
    close: &'a str,
    volume: &'a str,
}

#[derive(Deserialize, Debug)]
#[serde(try_from = "RawFrdCandle")]
pub struct FrdCandle {
    timestamp: DateTime<Utc>,
    high: Price,
    low: Price,
    open: Price,
    close: Price,
    volume: u64,
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

    // #[inline(always)]
    pub fn unchecked_convert_str_with_tz_to_utc_timestamp(s: &str, tz: Tz) -> DateTime<Utc> {
        let b = s.as_bytes();

        #[inline(always)]
        fn d2(b: &[u8], i: usize) -> u32 {
            (b[i] - b'0') as u32 * 10 + (b[i + 1] - b'0') as u32
        }

        let year = d2(b, 0) * 100 + d2(b, 2); // "20","25" -> 2025
        let month = d2(b, 5);
        let day = d2(b, 8);
        let hour = d2(b, 11);
        let min = d2(b, 14);
        let sec = d2(b, 17);

        let naive = chrono::NaiveDate::from_ymd_opt(year as i32, month, day)
            .expect("valid date")
            .and_hms_opt(hour, min, sec)
            .expect("valid time");

        tz.from_local_datetime(&naive)
            .single() // see hazard note; use .earliest() to tolerate overlaps
            .expect("unambiguous local time")
            .with_timezone(&Utc)
    }

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

    pub fn from_frd_csv_line_unchecked(s: &str) -> Result<Self, FrdCandleParsingError> {
        let mut split = s.trim_end().split(',');

        let raw_ts = split
            .next()
            .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Timestamp))?;
        let utc_ts = Self::unchecked_convert_str_with_tz_to_utc_timestamp(raw_ts, ExchangeTZ);
        let high = Price::from_str_unchecked(
            split
                .next()
                .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Price))?,
        );
        let low = Price::from_str_unchecked(
            split
                .next()
                .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Price))?,
        );
        let open = Price::from_str_unchecked(
            split
                .next()
                .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Price))?,
        );
        let close = Price::from_str_unchecked(
            split
                .next()
                .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Price))?,
        );
        let volume: u64 = split
            .next()
            .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Volume))?
            .parse()
            .map_err(|err| FrdCandleParsingError::VolumeParsingError(err))?;

        Ok(FrdCandle::new(utc_ts, high, low, open, close, volume))
    }

    pub fn from_frd_csv_line(s: &str) -> Result<Self, FrdCandleParsingError> {
        let mut split = s.trim().split(',');

        let raw_ts = split
            .next()
            .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Timestamp))?;
        let utc_ts = Self::convert_str_with_tz_to_utc_timestamp(raw_ts, ExchangeTZ)?;
        let high = Price::from_str(
            split
                .next()
                .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Price))?,
        )
        .map_err(|err| FrdCandleParsingError::PriceParsingError(err))?;
        let low = Price::from_str(
            split
                .next()
                .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Price))?,
        )
        .map_err(|err| FrdCandleParsingError::PriceParsingError(err))?;
        let open = Price::from_str(
            split
                .next()
                .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Price))?,
        )
        .map_err(|err| FrdCandleParsingError::PriceParsingError(err))?;
        let close = Price::from_str(
            split
                .next()
                .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Price))?,
        )
        .map_err(|err| FrdCandleParsingError::PriceParsingError(err))?;
        let volume: u64 = split
            .next()
            .ok_or_else(|| FrdCandleParsingError::Missing(FrdField::Volume))?
            .parse()
            .map_err(|err| FrdCandleParsingError::VolumeParsingError(err))?;

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
    PriceParsingError(ParsePriceError),
    VolumeParsingError(ParseIntError),
}

impl Display for FrdCandleParsingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FrdCandleParsingError::Missing(field) => write!(f, "Missing field: {:?}", field),
            FrdCandleParsingError::PriceParsingError(err) => err.fmt(f),
            FrdCandleParsingError::TimezoneConversionError(err) => err.fmt(f),
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

        let open =
            Price::from_str(value.open).map_err(|e| FrdCandleParsingError::PriceParsingError(e))?;
        let close = Price::from_str(value.close)
            .map_err(|e| FrdCandleParsingError::PriceParsingError(e))?;
        let high =
            Price::from_str(value.high).map_err(|e| FrdCandleParsingError::PriceParsingError(e))?;
        let low =
            Price::from_str(value.low).map_err(|e| FrdCandleParsingError::PriceParsingError(e))?;
        let volume: u64 = value
            .volume
            .parse()
            .map_err(|e| FrdCandleParsingError::VolumeParsingError(e))?;

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

#[cfg(test)]
mod tests {}
