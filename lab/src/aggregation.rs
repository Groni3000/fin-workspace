use chrono::{
    DateTime, Datelike, LocalResult, NaiveDate, NaiveTime, TimeDelta, TimeZone, Timelike, Utc,
};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};
use tradeprim::price::Price;

use crate::market_data::{Candle, RelevantPrice, Timestamped};

/// Aggregated OHLCV. `ts` is the bucket start.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Bar {
    /// Bucket start
    ts: DateTime<Utc>,
    open: Price,
    high: Price,
    low: Price,
    close: Price,
    volume: u64,
}

impl Bar {
    pub fn new(
        ts: DateTime<Utc>,
        open: Price,
        high: Price,
        low: Price,
        close: Price,
        volume: u64,
    ) -> Self {
        Self {
            ts,
            open,
            high,
            low,
            close,
            volume,
        }
    }

    fn seed<C: Candle>(ts: DateTime<Utc>, c: &C) -> Self {
        Self {
            ts,
            open: c.open(),
            high: c.high(),
            low: c.low(),
            close: c.close(),
            volume: c.volume(),
        }
    }

    fn merge<C: Candle>(&mut self, c: &C) {
        self.high = self.high.max(c.high());
        self.low = self.low.min(c.low());
        self.close = c.close();
        self.volume += c.volume();
    }
}

impl Timestamped for Bar {
    fn timestamp(&self) -> DateTime<Utc> {
        self.ts
    }
}

impl RelevantPrice for Bar {
    fn last_price(&self) -> Price {
        self.close
    }
}

impl Candle for Bar {
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

/// Midnight does not exist in every zone on every date
/// We add +1h when it doesn't.
fn local_midnight_utc(tz: Tz, date: NaiveDate) -> DateTime<Utc> {
    let naive = date.and_hms_opt(0, 0, 0).expect("midnight is a valid time");
    match tz.from_local_datetime(&naive) {
        LocalResult::Single(dt) => dt.with_timezone(&Utc),
        LocalResult::Ambiguous(earliest, _) => earliest.with_timezone(&Utc),
        LocalResult::None => tz
            .from_local_datetime(&date.and_hms_opt(1, 0, 0).expect("01:00 is a valid time"))
            .earliest()
            .expect("a DST gap never spans a full hour")
            .with_timezone(&Utc),
    }
}

fn local_to_utc(tz: Tz, date: NaiveDate, time: NaiveTime) -> DateTime<Utc> {
    match tz.from_local_datetime(&date.and_time(time)) {
        LocalResult::Single(dt) => dt.with_timezone(&Utc),
        LocalResult::Ambiguous(earliest, _) => earliest.with_timezone(&Utc),
        LocalResult::None => {
            local_midnight_utc(tz, date)
                + TimeDelta::seconds(time.num_seconds_from_midnight() as i64)
        }
    }
}

/// Fixed-interval OHLCV aggregation. The grid restarts at `bucket_origin` local time each day
/// (local midnight when unset), so a bucket always opens exactly at the origin regardless of DST.
#[derive(Debug)]
pub struct CandleAggregator {
    interval: i64,
    origin: NaiveTime,
    tz: Tz,
    candle: Option<Bar>,
    /// Cached `[this origin, next origin)` in UTC; avoids a tz lookup per record.
    window: Option<(DateTime<Utc>, DateTime<Utc>)>,
    last_ts: DateTime<Utc>,
}

impl CandleAggregator {
    pub fn new(interval: TimeDelta, bucket_origin: Option<NaiveTime>, tz: Tz) -> Self {
        let interval = interval.num_seconds();
        assert!(interval > 0, "interval must be positive");
        Self {
            interval,
            origin: bucket_origin.unwrap_or(NaiveTime::MIN),
            tz,
            candle: None,
            window: None,
            last_ts: DateTime::<Utc>::MIN_UTC,
        }
    }

    pub fn candle(&self) -> Option<&Bar> {
        self.candle.as_ref()
    }

    /// Emit the in-progress bar without waiting for the next bucket.
    pub fn flush(&mut self) -> Option<Bar> {
        self.candle.take()
    }

    /// The most recent occurrence of `origin` at or before `ts`. No timezone lookup while `ts`
    /// stays inside the cached window.
    fn anchor(&mut self, ts: DateTime<Utc>) -> DateTime<Utc> {
        if let Some((start, end)) = self.window
            && ts >= start
            && ts < end
        {
            return start;
        }
        let date = ts.with_timezone(&self.tz).date_naive();
        let today = local_to_utc(self.tz, date, self.origin);
        let (start, end) = if ts < today {
            (
                local_to_utc(
                    self.tz,
                    date.pred_opt().expect("date is not MIN"),
                    self.origin,
                ),
                today,
            )
        } else {
            (
                today,
                local_to_utc(
                    self.tz,
                    date.succ_opt().expect("date is not MAX"),
                    self.origin,
                ),
            )
        };
        self.window = Some((start, end));

        start
    }

    fn bucket_start(&mut self, ts: DateTime<Utc>) -> DateTime<Utc> {
        let anchor = self.anchor(ts);
        // `anchor <= ts` by construction, so plain flooring is enough.
        let floored = (ts - anchor).num_seconds() / self.interval * self.interval;

        anchor + TimeDelta::seconds(floored)
    }

    /// Updates the aggregator with a new candle, returning the aggregated bar if it completes a bucket.
    pub fn update<C: Candle>(&mut self, c: &C) -> Option<Bar> {
        debug_assert!(
            c.timestamp() >= self.last_ts,
            "input stream must be ordered"
        );
        self.last_ts = c.timestamp();
        let bucket = self.bucket_start(c.timestamp());
        match &mut self.candle {
            Some(cur) if cur.ts == bucket => {
                cur.merge(c);
                None
            }
            _ => self.candle.replace(Bar::seed(bucket, c)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SessionType {
    OneDay,
    Overnight,
}

/// One bar per trading session. Emitted bars are stamped at the session open, so their local
/// date is the session's own calendar day even when the session opens the evening before.
#[derive(Debug)]
pub struct SessionAggregator {
    start_time: NaiveTime,
    end_time: NaiveTime,
    session_type: SessionType,
    tz: Tz,
    candle: Option<Bar>,
    current_key: Option<NaiveDate>,
    outside_session: u64,
    last_ts: DateTime<Utc>,
}

impl SessionAggregator {
    pub fn new(start_time: NaiveTime, end_time: NaiveTime, tz: Tz) -> Self {
        let session_type = if start_time < end_time {
            SessionType::OneDay
        } else {
            SessionType::Overnight
        };
        Self {
            start_time,
            end_time,
            session_type,
            tz,
            candle: None,
            current_key: None,
            outside_session: 0,
            last_ts: DateTime::<Utc>::MIN_UTC,
        }
    }

    pub fn session_type(&self) -> SessionType {
        self.session_type
    }

    pub fn candle(&self) -> Option<&Bar> {
        self.candle.as_ref()
    }

    pub fn current_key(&self) -> Option<NaiveDate> {
        self.current_key
    }

    /// Records falling outside `[start_time, end_time)`; a non-zero count on liquid data
    /// means the session window is misconfigured.
    pub fn outside_session(&self) -> u64 {
        self.outside_session
    }

    pub fn flush(&mut self) -> Option<Bar> {
        self.current_key = None;
        self.candle.take()
    }

    pub fn within_session(&self, t: NaiveTime) -> bool {
        match self.session_type {
            SessionType::OneDay => self.start_time <= t && t < self.end_time,
            SessionType::Overnight => t >= self.start_time || t < self.end_time,
        }
    }

    /// The trading day a record belongs to. Overnight records at/after the open roll to the next.
    fn session_key(&self, local: DateTime<Tz>) -> NaiveDate {
        match self.session_type {
            SessionType::OneDay => local.date_naive(),
            SessionType::Overnight if local.time() >= self.start_time => {
                local.date_naive().succ_opt().expect("date is not MAX")
            }
            SessionType::Overnight => local.date_naive(),
        }
    }

    fn session_open(&self, key: NaiveDate) -> DateTime<Utc> {
        let date = match self.session_type {
            SessionType::OneDay => key,
            SessionType::Overnight => key.pred_opt().expect("date is not MIN"),
        };

        local_to_utc(self.tz, date, self.start_time)
    }

    pub fn update<C: Candle>(&mut self, c: &C) -> Option<Bar> {
        debug_assert!(
            c.timestamp() >= self.last_ts,
            "input stream must be ordered"
        );
        self.last_ts = c.timestamp();
        let local = c.timestamp().with_timezone(&self.tz);
        if !self.within_session(local.time()) {
            self.outside_session += 1;
            return None;
        }
        let key = self.session_key(local);
        match self.current_key {
            Some(current) if current == key => {
                self.candle
                    .as_mut()
                    .expect("a keyed session always holds a candle")
                    .merge(c);
                None
            }
            _ => {
                self.current_key = Some(key);
                self.candle.replace(Bar::seed(self.session_open(key), c))
            }
        }
    }
}

/// Daily bars into Sunday-start weeks (Sun->Sat), matching pandas `to_period("W-SAT")`. ISO weeks
/// would shear a Sunday-evening futures open into the previous week.
#[derive(Debug)]
pub struct WeekAggregator {
    tz: Tz,
    candle: Option<Bar>,
    current_week_start: Option<NaiveDate>,
    last_ts: DateTime<Utc>,
}

impl WeekAggregator {
    pub fn new(tz: Tz) -> Self {
        Self {
            tz,
            candle: None,
            current_week_start: None,
            last_ts: DateTime::<Utc>::MIN_UTC,
        }
    }

    pub fn candle(&self) -> Option<&Bar> {
        self.candle.as_ref()
    }

    pub fn current_week_start(&self) -> Option<NaiveDate> {
        self.current_week_start
    }

    pub fn flush(&mut self) -> Option<Bar> {
        self.current_week_start = None;
        self.candle.take()
    }

    /// Days since the most recent Sunday; 0 when `d` is itself a Sunday.
    fn week_start(d: NaiveDate) -> NaiveDate {
        let back = (d.weekday().num_days_from_monday() + 1) % 7;

        d - TimeDelta::days(back as i64)
    }

    pub fn update<C: Candle>(&mut self, daily: &C) -> Option<Bar> {
        debug_assert!(
            daily.timestamp() >= self.last_ts,
            "input stream must be ordered"
        );
        self.last_ts = daily.timestamp();
        let local_date = daily.timestamp().with_timezone(&self.tz).date_naive();
        let week_start = Self::week_start(local_date);
        match self.current_week_start {
            Some(current) if current == week_start => {
                self.candle
                    .as_mut()
                    .expect("a keyed week always holds a candle")
                    .merge(daily);
                None
            }
            _ => {
                self.current_week_start = Some(week_start);
                self.candle.replace(Bar::seed(daily.timestamp(), daily))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use chrono_tz::US::Eastern;

    fn p(s: &str) -> Price {
        Price::from_str_unchecked(s)
    }

    /// A bar at `local` on `date` in Eastern, with all four prices equal.
    fn at(date: (i32, u32, u32), time: (u32, u32, u32), price: &str, volume: u64) -> Bar {
        let naive = NaiveDate::from_ymd_opt(date.0, date.1, date.2)
            .unwrap()
            .and_hms_opt(time.0, time.1, time.2)
            .unwrap();
        let ts = Eastern
            .from_local_datetime(&naive)
            .earliest()
            .unwrap()
            .with_timezone(&Utc);

        ohlc(ts, price, price, price, price, volume)
    }

    fn ohlc(ts: DateTime<Utc>, open: &str, high: &str, low: &str, close: &str, volume: u64) -> Bar {
        Bar::new(ts, p(open), p(high), p(low), p(close), volume)
    }

    fn utc(date: (i32, u32, u32), time: (u32, u32, u32)) -> DateTime<Utc> {
        Utc.with_ymd_and_hms(date.0, date.1, date.2, time.0, time.1, time.2)
            .unwrap()
    }

    // --- DST: the two bugs I encountered ---

    /// Fall-back 2008-11-02: 01:30 EDT and 01:30 EST are two real instants an hour apart and
    /// must not collapse into one bucket.
    #[test]
    fn fall_back_does_not_collapse_repeated_local_hour() {
        let mut agg = CandleAggregator::new(TimeDelta::minutes(15), None, Eastern);
        // 01:30 EDT = 05:30Z, 01:30 EST = 06:30Z.
        let first = ohlc(utc((2008, 11, 2), (5, 30, 0)), "1", "1", "1", "1", 1);
        let second = ohlc(utc((2008, 11, 2), (6, 30, 0)), "2", "2", "2", "2", 1);

        assert!(agg.update(&first).is_none());
        let completed = agg.update(&second).expect("second bar opens a new bucket");
        assert_eq!(completed.close(), p("1"));
        assert_eq!(completed.volume(), 1);
    }

    /// The 25-hour fall-back day still yields whole buckets, and the last one ends at midnight.
    #[test]
    fn fall_back_day_grid_reaches_next_midnight() {
        let mut agg = CandleAggregator::new(TimeDelta::hours(1), None, Eastern);
        // 23:30 EST = 04:30Z on the 3rd; the day started at 04:00Z on the 2nd (25h).
        let last = ohlc(utc((2008, 11, 3), (4, 30, 0)), "1", "1", "1", "1", 1);
        agg.update(&last);

        assert_eq!(
            agg.candle().unwrap().timestamp(),
            utc((2008, 11, 3), (4, 0, 0))
        );
        // Next local midnight opens a fresh day anchor.
        let midnight = ohlc(utc((2008, 11, 3), (5, 0, 0)), "2", "2", "2", "2", 1);
        let completed = agg.update(&midnight).expect("new day, new bucket");
        assert_eq!(completed.timestamp(), utc((2008, 11, 3), (4, 0, 0)));
        assert_eq!(
            agg.candle().unwrap().timestamp(),
            utc((2008, 11, 3), (5, 0, 0))
        );
    }

    /// Spring-forward 2008-03-09: 02:00-03:00 local does not exist, so the grid must jump.
    #[test]
    fn spring_forward_skips_missing_hour() {
        let mut agg = CandleAggregator::new(TimeDelta::hours(1), None, Eastern);
        // 01:30 EST = 06:30Z, 03:30 EDT = 07:30Z: adjacent real hours.
        let before = ohlc(utc((2008, 3, 9), (6, 30, 0)), "1", "1", "1", "1", 1);
        let after = ohlc(utc((2008, 3, 9), (7, 30, 0)), "2", "2", "2", "2", 1);

        agg.update(&before);
        assert_eq!(
            agg.candle().unwrap().timestamp(),
            utc((2008, 3, 9), (6, 0, 0))
        );
        let completed = agg.update(&after).expect("next hour bucket");
        assert_eq!(completed.close(), p("1"));
        assert_eq!(
            agg.candle().unwrap().timestamp(),
            utc((2008, 3, 9), (7, 0, 0))
        );
    }

    // --- Grid origin ---

    /// With origin 18:00 and a 15m interval the RB halt (17:00-18:00) sits on a boundary, so
    /// no bucket spans it.
    #[test]
    fn origin_aligned_grid_does_not_span_the_halt() {
        let origin = NaiveTime::from_hms_opt(18, 0, 0).unwrap();
        let mut agg = CandleAggregator::new(TimeDelta::minutes(15), Some(origin), Eastern);

        let before_close = at((2025, 6, 10), (16, 58, 0), "1", 1);
        let after_open = at((2025, 6, 10), (18, 1, 0), "2", 1);

        agg.update(&before_close);
        assert_eq!(
            agg.candle().unwrap().timestamp(),
            at((2025, 6, 10), (16, 45, 0), "0", 0).timestamp()
        );
        let completed = agg.update(&after_open).expect("new bucket after the halt");
        assert_eq!(completed.close(), p("1"));
        assert_eq!(
            agg.candle().unwrap().timestamp(),
            at((2025, 6, 10), (18, 0, 0), "0", 0).timestamp()
        );
    }

    /// 90m does not divide Eastern's -4h offset, so the grid only lands on local 09:00 if it is
    /// anchored at local midnight. A UTC-anchored grid gives 09:30.
    #[test]
    fn grid_is_anchored_at_local_midnight() {
        let mut agg = CandleAggregator::new(TimeDelta::minutes(90), None, Eastern);

        agg.update(&at((2025, 6, 10), (10, 0, 0), "1", 1));

        assert_eq!(
            agg.candle().unwrap().timestamp(),
            at((2025, 6, 10), (9, 0, 0), "0", 0).timestamp()
        );
    }

    /// The grid follows local 18:00 across DST; a UTC-anchored grid would drift by an hour.
    #[test]
    fn origin_holds_local_time_across_dst() {
        let origin = NaiveTime::from_hms_opt(18, 0, 0).unwrap();

        for date in [(2025, 1, 10), (2025, 6, 10)] {
            let mut agg = CandleAggregator::new(TimeDelta::minutes(15), Some(origin), Eastern);
            agg.update(&at(date, (18, 1, 0), "1", 1));

            assert_eq!(
                agg.candle().unwrap().timestamp(),
                at(date, (18, 0, 0), "0", 0).timestamp(),
                "{date:?}"
            );
        }
    }

    /// On the 23-hour spring-forward day the origin still lands on local 18:00.
    #[test]
    fn origin_lands_on_local_open_on_spring_forward_day() {
        let origin = NaiveTime::from_hms_opt(18, 0, 0).unwrap();
        let mut agg = CandleAggregator::new(TimeDelta::minutes(15), Some(origin), Eastern);

        agg.update(&at((2008, 3, 9), (18, 5, 0), "1", 1));

        assert_eq!(
            agg.candle().unwrap().timestamp(),
            utc((2008, 3, 9), (22, 0, 0))
        );
    }

    /// An interval that does not divide the DST shift still opens a bucket exactly at the origin;
    /// a midnight-anchored grid gave 17:30 here.
    #[test]
    fn non_dividing_interval_still_opens_at_origin_on_spring_forward() {
        let origin = NaiveTime::from_hms_opt(18, 0, 0).unwrap();

        for date in [(2008, 3, 8), (2008, 3, 9)] {
            let mut agg = CandleAggregator::new(TimeDelta::minutes(90), Some(origin), Eastern);
            agg.update(&at(date, (18, 0, 0), "1", 1));

            assert_eq!(
                agg.candle().unwrap().timestamp(),
                at(date, (18, 0, 0), "0", 0).timestamp(),
                "{date:?}"
            );
        }
    }

    /// A record earlier in the day than the origin belongs to the previous day's anchor.
    #[test]
    fn record_before_origin_uses_previous_anchor() {
        let origin = NaiveTime::from_hms_opt(18, 0, 0).unwrap();
        let mut agg = CandleAggregator::new(TimeDelta::minutes(15), Some(origin), Eastern);

        agg.update(&at((2025, 6, 10), (9, 37, 0), "1", 1));

        assert_eq!(
            agg.candle().unwrap().timestamp(),
            at((2025, 6, 10), (9, 30, 0), "0", 0).timestamp()
        );
    }

    // --- Ordering ---

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "input stream must be ordered")]
    fn out_of_order_record_trips_the_assert() {
        let mut agg = CandleAggregator::new(TimeDelta::minutes(15), None, Eastern);

        agg.update(&at((2025, 6, 10), (10, 16, 0), "1", 1));
        agg.update(&at((2025, 6, 10), (10, 5, 0), "2", 1));
    }

    // --- Sessions ---

    /// An overnight session opening 18:00 belongs to the *next* trading day.
    #[test]
    fn overnight_key_rolls_to_next_day() {
        let mut agg = SessionAggregator::new(
            NaiveTime::from_hms_opt(18, 0, 0).unwrap(),
            NaiveTime::from_hms_opt(17, 0, 0).unwrap(),
            Eastern,
        );
        assert_eq!(agg.session_type(), SessionType::Overnight);

        agg.update(&at((2025, 6, 8), (18, 30, 0), "1", 1));
        assert_eq!(
            agg.current_key(),
            Some(NaiveDate::from_ymd_opt(2025, 6, 9).unwrap())
        );

        // Monday morning is the same session.
        assert!(agg.update(&at((2025, 6, 9), (9, 30, 0), "2", 1)).is_none());
        assert_eq!(
            agg.current_key(),
            Some(NaiveDate::from_ymd_opt(2025, 6, 9).unwrap())
        );
    }

    /// The emitted daily bar is stamped at the session open, not at its first record.
    #[test]
    fn session_bar_is_stamped_at_session_open() {
        let mut agg = SessionAggregator::new(
            NaiveTime::from_hms_opt(18, 0, 0).unwrap(),
            NaiveTime::from_hms_opt(17, 0, 0).unwrap(),
            Eastern,
        );

        agg.update(&at((2025, 6, 8), (18, 3, 0), "1", 1));
        let completed = agg
            .update(&at((2025, 6, 9), (18, 30, 0), "2", 1))
            .expect("second session closes the first");

        assert_eq!(
            completed.timestamp(),
            at((2025, 6, 8), (18, 0, 0), "0", 0).timestamp()
        );
    }

    #[test]
    fn outside_session_records_are_counted_not_aggregated() {
        let mut agg = SessionAggregator::new(
            NaiveTime::from_hms_opt(9, 30, 0).unwrap(),
            NaiveTime::from_hms_opt(16, 0, 0).unwrap(),
            Eastern,
        );
        assert_eq!(agg.session_type(), SessionType::OneDay);

        assert!(agg.update(&at((2025, 6, 10), (8, 0, 0), "1", 1)).is_none());
        assert!(agg.update(&at((2025, 6, 10), (16, 0, 0), "2", 1)).is_none());

        assert_eq!(agg.outside_session(), 2);
        assert!(agg.candle().is_none());
    }

    // --- Weeks ---

    /// A Sunday-evening open starts the week; the Friday session closes it.
    #[test]
    fn sunday_open_starts_the_week() {
        let mut week = WeekAggregator::new(Eastern);
        let sunday = at((2025, 6, 8), (18, 0, 0), "1", 1);
        let friday = at((2025, 6, 13), (18, 0, 0), "2", 1);

        assert!(week.update(&sunday).is_none());
        assert_eq!(
            week.current_week_start(),
            Some(NaiveDate::from_ymd_opt(2025, 6, 8).unwrap())
        );
        assert!(week.update(&friday).is_none());
        assert_eq!(
            week.current_week_start(),
            Some(NaiveDate::from_ymd_opt(2025, 6, 8).unwrap())
        );

        let next_sunday = at((2025, 6, 15), (18, 0, 0), "3", 1);
        let completed = week.update(&next_sunday).expect("new week");
        assert_eq!(completed.open(), p("1"));
        assert_eq!(completed.close(), p("2"));
    }

    mod preserve_behavior {
        use super::*;

        #[test]
        fn merges_ohlcv_within_a_bucket() {
            let mut agg = CandleAggregator::new(TimeDelta::minutes(15), None, Eastern);
            let base = at((2025, 6, 10), (10, 0, 0), "0", 0).timestamp();

            agg.update(&ohlc(base, "10", "12", "9", "11", 5));
            agg.update(&ohlc(
                base + TimeDelta::minutes(1),
                "11",
                "15",
                "8",
                "14",
                7,
            ));
            let completed = agg
                .update(&at((2025, 6, 10), (10, 15, 0), "20", 1))
                .expect("bucket rolled");

            assert_eq!(completed.open(), p("10"));
            assert_eq!(completed.high(), p("15"));
            assert_eq!(completed.low(), p("8"));
            assert_eq!(completed.close(), p("14"));
            assert_eq!(completed.volume(), 12);
        }

        #[test]
        fn first_record_emits_nothing() {
            let mut agg = CandleAggregator::new(TimeDelta::minutes(15), None, Eastern);

            assert!(agg.update(&at((2025, 6, 10), (10, 0, 0), "1", 1)).is_none());
        }

        #[test]
        fn flush_emits_the_open_bucket() {
            let mut agg = CandleAggregator::new(TimeDelta::minutes(15), None, Eastern);
            agg.update(&at((2025, 6, 10), (10, 0, 0), "1", 3));

            let flushed = agg.flush().expect("in-progress bar");
            assert_eq!(flushed.volume(), 3);
            assert!(agg.flush().is_none());
        }

        #[test]
        fn bar_is_a_candle() {
            let bar = ohlc(utc((2025, 6, 10), (14, 0, 0)), "1", "2", "0.5", "1.5", 9);

            assert_eq!(bar.last_price(), p("1.5"));
            assert_eq!(bar.timestamp(), utc((2025, 6, 10), (14, 0, 0)));
        }

        #[test]
        fn session_chains_into_week() {
            let mut session = SessionAggregator::new(
                NaiveTime::from_hms_opt(18, 0, 0).unwrap(),
                NaiveTime::from_hms_opt(17, 0, 0).unwrap(),
                Eastern,
            );
            let mut week = WeekAggregator::new(Eastern);

            for (date, price) in [
                ((2025, 6, 8), "1"),
                ((2025, 6, 9), "2"),
                ((2025, 6, 10), "3"),
            ] {
                if let Some(daily) = session.update(&at(date, (18, 0, 0), price, 1)) {
                    week.update(&daily);
                }
            }

            assert_eq!(week.candle().unwrap().open(), p("1"));
            assert_eq!(week.candle().unwrap().volume(), 2);
        }
    }
}
