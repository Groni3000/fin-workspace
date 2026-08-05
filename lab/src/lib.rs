pub mod event;
pub mod event_loop;
pub mod events_impls;
pub mod formats;
pub mod market_data;
pub mod oms;
pub mod portfolio;
pub mod rms;
pub mod strategy;

use chrono::{DateTime, FixedOffset, NaiveDate, NaiveDateTime, Offset, TimeZone, Utc};
use chrono_tz::Tz;

use crate::market_data::{Candle, MarketData};

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
    }

    Ok((lines, last))
}

// TODO: OffsetCache should have tests... A lot of tests...

/// Instead of using chrono-tz's lookup table for Tz,
/// we cache fixed offset and use it.
///
/// Each day we take `(day_start, day_end)` and check offsets.
/// - If they are the same - use cached FixedOffset.
/// - If they are different - recompute offset for each record for this day.
///
/// In such way we avoid redundant lookups to two days per year.
pub struct OffsetCache {
    date: Option<NaiveDate>,
    offset: FixedOffset,
    /// If this day is not a transition day - use FixedOffset
    /// else - look up the offset for each record during this day.
    constant_day: bool,
}

impl OffsetCache {
    pub fn new() -> Self {
        Self {
            date: None,
            offset: FixedOffset::east_opt(0).unwrap(),
            constant_day: false,
        }
    }

    /// Convert to Utc, using cached FixedOffset during `constant_day`
    pub fn to_utc(&mut self, naive: NaiveDateTime, tz: Tz) -> DateTime<Utc> {
        let date = naive.date();

        if self.date != Some(date) {
            // New day: take both ends, check their offsets.
            let start = date.and_hms_opt(0, 0, 0).unwrap();
            let end = date.and_hms_opt(23, 59, 59).unwrap();
            let off_start = Self::lookup(tz, start);
            let off_end = Self::lookup(tz, end);

            self.date = Some(date);
            self.constant_day = off_start == off_end;
            self.offset = off_start;
        }

        if self.constant_day {
            // Apply the fixed offset
            self.offset
                .from_local_datetime(&naive)
                .single()
                .expect("a fixed offset is never ambiguous")
                .with_timezone(&Utc)
        } else {
            // Transition day: full, correct lookup for this row.
            match tz.from_local_datetime(&naive) {
                chrono::LocalResult::Single(ts) => ts.with_timezone(&Utc),
                chrono::LocalResult::Ambiguous(a, _) => a.with_timezone(&Utc),
                chrono::LocalResult::None => {
                    panic!("Non existent local time {:?} for timezone {:?}", naive, tz);
                }
            }
        }
    }

    /// Get FixedOffset
    fn lookup(tz: Tz, naive: NaiveDateTime) -> FixedOffset {
        tz.offset_from_local_datetime(&naive)
            .single()
            .expect("midnight/end-of-day is never a DST transition for exchange zones")
            .fix()
    }
}

impl Default for OffsetCache {
    fn default() -> Self {
        Self::new()
    }
}

/// It's better not to use it :/
pub(crate) mod untested {
    use crate::OffsetCache;
    use crate::formats::frd::{FrdCandle, FrdCandleParsingError, FrdField};
    use chrono::{NaiveDate, NaiveDateTime};
    use chrono_tz::US::Eastern as ExchangeTz;
    use tradeprim::price::Price;

    impl FrdCandle {
        /// Parse the fixed-width `YYYY-MM-DD HH:MM:SS` field into a naive local
        /// datetime. Unchecked: assumes exactly that 19-byte ASCII layout.
        pub fn parse_naive_frd_unchecked(s: &str) -> NaiveDateTime {
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

            NaiveDate::from_ymd_opt(year as i32, month, day)
                .expect("valid date")
                .and_hms_opt(hour, min, sec)
                .expect("valid time")
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
        pub unsafe fn from_frd_csv_line_unchecked(
            bytes: &[u8],
            tz_cache: &mut OffsetCache,
        ) -> Result<Self, FrdCandleParsingError> {
            let s = unsafe { str::from_utf8_unchecked(bytes) };
            let trimmed = s.trim_end();

            let naive = Self::parse_naive_frd_unchecked(&trimmed[..19]);
            let utc_ts = tz_cache.to_utc(naive, ExchangeTz);

            // `,` is ommited
            let mut split = trimmed[20..].split(',');
            let high = Price::from_str_unchecked(
                split
                    .next()
                    .ok_or(FrdCandleParsingError::Missing(FrdField::Price))?,
            );
            let low = Price::from_str_unchecked(
                split
                    .next()
                    .ok_or(FrdCandleParsingError::Missing(FrdField::Price))?,
            );
            let open = Price::from_str_unchecked(
                split
                    .next()
                    .ok_or(FrdCandleParsingError::Missing(FrdField::Price))?,
            );
            let close = Price::from_str_unchecked(
                split
                    .next()
                    .ok_or(FrdCandleParsingError::Missing(FrdField::Price))?,
            );
            let volume: u64 = split
                .next()
                .ok_or(FrdCandleParsingError::Missing(FrdField::Volume))?
                .parse()
                .map_err(FrdCandleParsingError::VolumeParsingError)?;

            Ok(FrdCandle::new(utc_ts, high, low, open, close, volume))
        }
    }
}

#[cfg(test)]
mod tests {}
