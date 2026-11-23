pub mod aggregation;
pub mod formats;
pub mod strats_impl;

use jiff::{
    Timestamp,
    civil::{Date, DateTime},
    tz::{AmbiguousOffset, Offset, TimeZone},
};

use mdata::{Candle, MarketData};

/// === PROCESS MARKET DATA
pub fn process_md<T>(market_data: &mut T) -> Result<(u64, Option<T::Record>), T::Error>
where
    T: MarketData,
    T::Record: Candle,
{
    let mut lines: u64 = 0;
    let mut last: Option<T::Record> = None;

    while let Some(Ok(record)) = market_data.next() {
        lines += 1;
        last = Some(record);
        if lines.is_multiple_of(1_000) {
            println!("Processed {lines} lines\nLast processed line {last:?}");
        }
    }

    Ok((lines, last))
}

// TODO: OffsetCache should have tests... A lot of tests...

/// Instead of looking up the time zone for every record,
/// we cache the day's fixed offset and use it.
///
/// Each day we take `(day_start, day_end)` and check offsets.
/// - If they are the same - use the cached offset.
/// - If they are different - recompute offset for each record for this day.
///
/// In such way we avoid redundant lookups to two days per year.
pub struct OffsetCache {
    date: Option<Date>,
    offset: Offset,
    /// If this day is not a transition day - use the cached offset
    /// else - look up the offset for each record during this day.
    constant_day: bool,
}

impl OffsetCache {
    pub fn new() -> Self {
        Self {
            date: None,
            offset: Offset::UTC,
            constant_day: false,
        }
    }

    /// Convert to UTC, using the cached offset during `constant_day`
    pub fn to_utc(&mut self, local: DateTime, tz: &TimeZone) -> Timestamp {
        let date = local.date();

        if self.date != Some(date) {
            // New day: take both ends, check their offsets.
            let off_start = Self::lookup(tz, date.at(0, 0, 0, 0));
            let off_end = Self::lookup(tz, date.at(23, 59, 59, 0));

            self.date = Some(date);
            self.constant_day = off_start == off_end;
            self.offset = off_start;
        }

        if self.constant_day {
            // Apply the fixed offset
            self.offset
                .to_timestamp(local)
                .expect("a local time in range")
        } else {
            // Transition day: full, correct lookup for this row.
            let ts = tz.to_ambiguous_timestamp(local);
            match ts.offset() {
                AmbiguousOffset::Gap { .. } => {
                    panic!("Non existent local time {local} for timezone {tz:?}");
                }
                AmbiguousOffset::Unambiguous { .. } | AmbiguousOffset::Fold { .. } => {
                    ts.earlier().expect("a local time in range")
                }
            }
        }
    }

    /// The offset in effect at `local`.
    fn lookup(tz: &TimeZone, local: DateTime) -> Offset {
        match tz.to_ambiguous_timestamp(local).offset() {
            AmbiguousOffset::Unambiguous { offset } => offset,
            AmbiguousOffset::Gap { .. } | AmbiguousOffset::Fold { .. } => {
                panic!("midnight/end-of-day is never a DST transition for exchange zones")
            }
        }
    }
}

impl Default for OffsetCache {
    fn default() -> Self {
        Self::new()
    }
}

/// It's better not to use it :/
pub mod untested {
    use crate::OffsetCache;
    use crate::formats::frd::{EXCHANGE_TZ, Field, ParseError};
    use jiff::civil::DateTime;
    use mdata::Ohlcv;
    use tradeprim::{price::Price, volume::Volume};

    /// Parse the fixed-width `YYYY-MM-DD HH:MM:SS` field into a naive local
    /// datetime. Unchecked: assumes exactly that 19-byte ASCII layout.
    pub fn parse_naive_frd_unchecked(s: &str) -> DateTime {
        let b = s.as_bytes();

        #[inline(always)]
        fn d2(b: &[u8], i: usize) -> i8 {
            (b[i] - b'0') as i8 * 10 + (b[i + 1] - b'0') as i8
        }

        let year = i16::from(d2(b, 0)) * 100 + i16::from(d2(b, 2)); // "20","25" -> 2025
        let month = d2(b, 5);
        let day = d2(b, 8);
        let hour = d2(b, 11);
        let min = d2(b, 14);
        let sec = d2(b, 17);

        DateTime::new(year, month, day, hour, min, sec, 0).expect("valid date and time")
    }

    /// **DO NOT USE THIS FUNCTION**
    ///
    /// It is pretty much experimental, no validation, unsafe,
    /// time logic is not tested,...
    ///
    /// Unless you are ok to uphold some invariants of valid data
    /// and use untested cache,
    ///
    /// **DO NOT USE THIS FUNCTION**
    ///
    /// _Though it can give you ~1.7x speedup ;)_
    ///
    /// # Safety
    /// `bytes` should be valid utf-8
    pub unsafe fn parse_frd_line_unchecked(
        bytes: &[u8],
        tz_cache: &mut OffsetCache,
    ) -> Result<Ohlcv, ParseError> {
        let s = unsafe { str::from_utf8_unchecked(bytes) };
        let trimmed = s.trim_end();

        let naive = parse_naive_frd_unchecked(&trimmed[..19]);
        let ts = tz_cache.to_utc(naive, &EXCHANGE_TZ);

        // `,` is ommited
        let mut split = trimmed[20..].split(',');
        let mut price = || -> Result<Price, ParseError> {
            let field = split.next().ok_or(ParseError::Missing(Field::Price))?;
            Ok(Price::from_str_unchecked(field))
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
}

#[cfg(test)]
mod tests {}
