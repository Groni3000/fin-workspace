use jiff::{
    SignedDuration, Timestamp, ToSpan,
    civil::{Date, DateTime, Time},
    tz::{AmbiguousOffset, TimeZone},
};

use mdata::{Candle, HasTimestamp, HasVolume, Ohlcv};

/// `time` on `date` in `tz`. A repeated time (DST ends) is the earlier one. A skipped time (DST
/// starts) counts from the start of the day: the day's first instant plus `time` since midnight.
fn local_to_utc(tz: &TimeZone, date: Date, time: Time) -> Timestamp {
    let local = tz.to_ambiguous_timestamp(date.to_datetime(time));
    match local.offset() {
        AmbiguousOffset::Gap { .. } => {
            let start_of_day = date
                .to_zoned_datetime(tz.clone())
                .and_then(|day| day.start_of_day())
                .expect("every date has a start of day")
                .timestamp();
            start_of_day + Time::midnight().duration_until(time)
        }
        AmbiguousOffset::Unambiguous { .. } | AmbiguousOffset::Fold { .. } => {
            local.earlier().expect("a local time in range")
        }
    }
}

/// Fixed-interval OHLCV aggregation. The grid restarts at `bucket_origin` local time each day
/// (local midnight when unset), so a bucket always opens exactly at the origin regardless of DST.
#[derive(Debug)]
pub struct CandleAggregator {
    interval: i64,
    origin: Time,
    tz: TimeZone,
    candle: Option<Ohlcv>,
    /// Cached `[this origin, next origin)` in UTC; avoids a tz lookup per record.
    window: Option<(Timestamp, Timestamp)>,
    last_ts: Timestamp,
}

impl CandleAggregator {
    pub fn new(interval: SignedDuration, bucket_origin: Option<Time>, tz: TimeZone) -> Self {
        let interval = interval.as_secs();
        assert!(interval > 0, "interval must be positive");
        Self {
            interval,
            origin: bucket_origin.unwrap_or(Time::midnight()),
            tz,
            candle: None,
            window: None,
            last_ts: Timestamp::MIN,
        }
    }

    pub fn candle(&self) -> Option<&Ohlcv> {
        self.candle.as_ref()
    }

    /// Emit the in-progress bar without waiting for the next bucket.
    pub fn flush(&mut self) -> Option<Ohlcv> {
        self.candle.take()
    }

    /// The most recent occurrence of `origin` at or before `ts`. No timezone lookup while `ts`
    /// stays inside the cached window.
    fn anchor(&mut self, ts: Timestamp) -> Timestamp {
        if let Some((start, end)) = self.window
            && ts >= start
            && ts < end
        {
            return start;
        }
        let date = self.tz.to_datetime(ts).date();
        let today = local_to_utc(&self.tz, date, self.origin);
        let (start, end) = if ts < today {
            let yesterday = date.yesterday().expect("date is not MIN");
            (local_to_utc(&self.tz, yesterday, self.origin), today)
        } else {
            let tomorrow = date.tomorrow().expect("date is not MAX");
            (today, local_to_utc(&self.tz, tomorrow, self.origin))
        };
        self.window = Some((start, end));

        start
    }

    fn bucket_start(&mut self, ts: Timestamp) -> Timestamp {
        let anchor = self.anchor(ts);
        // `anchor <= ts` by construction, so plain flooring is enough.
        let floored = ts.duration_since(anchor).as_secs() / self.interval * self.interval;

        anchor + SignedDuration::from_secs(floored)
    }

    /// Updates the aggregator with a new candle, returning the aggregated bar if it completes a bucket.
    pub fn update<C: Candle + HasVolume>(&mut self, c: &C) -> Option<Ohlcv> {
        let ts = c.timestamp();
        debug_assert!(ts >= self.last_ts, "input stream must be ordered");
        self.last_ts = ts;
        let bucket = self.bucket_start(ts);
        match &mut self.candle {
            Some(cur) if cur.timestamp() == bucket => {
                cur.merge(c);
                None
            }
            _ => self.candle.replace(Ohlcv::seed(bucket, c)),
        }
    }

    pub fn interval(&self) -> i64 {
        self.interval
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
    start_time: Time,
    end_time: Time,
    session_type: SessionType,
    tz: TimeZone,
    candle: Option<Ohlcv>,
    current_key: Option<Date>,
    outside_session: u64,
    last_ts: Timestamp,
}

impl SessionAggregator {
    pub fn new(start_time: Time, end_time: Time, tz: TimeZone) -> Self {
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
            last_ts: Timestamp::MIN,
        }
    }

    pub fn session_type(&self) -> SessionType {
        self.session_type
    }

    pub fn candle(&self) -> Option<&Ohlcv> {
        self.candle.as_ref()
    }

    pub fn current_key(&self) -> Option<Date> {
        self.current_key
    }

    /// Records falling outside `[start_time, end_time)`; a non-zero count on liquid data
    /// means the session window is misconfigured.
    pub fn outside_session(&self) -> u64 {
        self.outside_session
    }

    pub fn flush(&mut self) -> Option<Ohlcv> {
        self.current_key = None;
        self.candle.take()
    }

    pub fn within_session(&self, t: Time) -> bool {
        match self.session_type {
            SessionType::OneDay => self.start_time <= t && t < self.end_time,
            SessionType::Overnight => t >= self.start_time || t < self.end_time,
        }
    }

    /// The trading day a record belongs to. Overnight records at/after the open roll to the next.
    fn session_key(&self, local: DateTime) -> Date {
        match self.session_type {
            SessionType::OneDay => local.date(),
            SessionType::Overnight if local.time() >= self.start_time => {
                local.date().tomorrow().expect("date is not MAX")
            }
            SessionType::Overnight => local.date(),
        }
    }

    fn session_open(&self, key: Date) -> Timestamp {
        let date = match self.session_type {
            SessionType::OneDay => key,
            SessionType::Overnight => key.yesterday().expect("date is not MIN"),
        };

        local_to_utc(&self.tz, date, self.start_time)
    }

    pub fn update<C: Candle + HasVolume>(&mut self, c: &C) -> Option<Ohlcv> {
        let ts = c.timestamp();
        debug_assert!(ts >= self.last_ts, "input stream must be ordered");
        self.last_ts = ts;
        let local = self.tz.to_datetime(ts);
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
                self.candle.replace(Ohlcv::seed(self.session_open(key), c))
            }
        }
    }
}

/// Daily bars into Sunday-start weeks (Sun->Sat), matching pandas `to_period("W-SAT")`. ISO weeks
/// would shear a Sunday-evening futures open into the previous week.
#[derive(Debug)]
pub struct WeekAggregator {
    tz: TimeZone,
    candle: Option<Ohlcv>,
    current_week_start: Option<Date>,
    last_ts: Timestamp,
}

impl WeekAggregator {
    pub fn new(tz: TimeZone) -> Self {
        Self {
            tz,
            candle: None,
            current_week_start: None,
            last_ts: Timestamp::MIN,
        }
    }

    pub fn candle(&self) -> Option<&Ohlcv> {
        self.candle.as_ref()
    }

    pub fn current_week_start(&self) -> Option<Date> {
        self.current_week_start
    }

    pub fn flush(&mut self) -> Option<Ohlcv> {
        self.current_week_start = None;
        self.candle.take()
    }

    /// The Sunday starting the week of `d`; `d` itself when it is a Sunday.
    fn week_start(d: Date) -> Date {
        d - d.weekday().to_sunday_zero_offset().days()
    }

    pub fn update<C: Candle + HasVolume>(&mut self, daily: &C) -> Option<Ohlcv> {
        let ts = daily.timestamp();
        debug_assert!(ts >= self.last_ts, "input stream must be ordered");
        self.last_ts = ts;
        let local_date = self.tz.to_datetime(ts).date();
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
                self.candle.replace(Ohlcv::seed(daily.timestamp(), daily))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use jiff::civil::{date, datetime, time};
    use tradeprim::{price::Price, volume::Volume};

    fn eastern() -> TimeZone {
        TimeZone::get("America/New_York").expect("the tz database has America/New_York")
    }

    fn p(s: &str) -> Price {
        Price::from_str_unchecked(s)
    }

    /// A bar at `local` on `date` in eastern(), with all four prices equal.
    fn at(date: (i16, i8, i8), time: (i8, i8, i8), price: &str, volume: u64) -> Ohlcv {
        let local = datetime(date.0, date.1, date.2, time.0, time.1, time.2, 0);
        let ts = eastern().to_ambiguous_timestamp(local).earlier().unwrap();

        ohlc(ts, price, price, price, price, volume)
    }

    fn ohlc(ts: Timestamp, open: &str, high: &str, low: &str, close: &str, volume: u64) -> Ohlcv {
        Ohlcv::new(
            ts,
            p(open),
            p(high),
            p(low),
            p(close),
            Volume::from_units(volume),
        )
    }

    fn utc(date: (i16, i8, i8), time: (i8, i8, i8)) -> Timestamp {
        datetime(date.0, date.1, date.2, time.0, time.1, time.2, 0)
            .to_zoned_datetime(TimeZone::UTC)
            .unwrap()
            .timestamp()
    }

    // --- DST: the two bugs I encountered ---

    /// Fall-back 2008-11-02: 01:30 EDT and 01:30 EST are two real instants an hour apart and
    /// must not collapse into one bucket.
    #[test]
    fn fall_back_does_not_collapse_repeated_local_hour() {
        let mut agg = CandleAggregator::new(SignedDuration::from_mins(15), None, eastern());
        // 01:30 EDT = 05:30Z, 01:30 EST = 06:30Z.
        let first = ohlc(utc((2008, 11, 2), (5, 30, 0)), "1", "1", "1", "1", 1);
        let second = ohlc(utc((2008, 11, 2), (6, 30, 0)), "2", "2", "2", "2", 1);

        assert!(agg.update(&first).is_none());
        let completed = agg.update(&second).expect("second bar opens a new bucket");
        assert_eq!(completed.close(), p("1"));
        assert_eq!(completed.volume(), Volume::from_units(1));
    }

    /// The 25-hour fall-back day still yields whole buckets, and the last one ends at midnight.
    #[test]
    fn fall_back_day_grid_reaches_next_midnight() {
        let mut agg = CandleAggregator::new(SignedDuration::from_hours(1), None, eastern());
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
        let mut agg = CandleAggregator::new(SignedDuration::from_hours(1), None, eastern());
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
        let origin = time(18, 0, 0, 0);
        let mut agg = CandleAggregator::new(SignedDuration::from_mins(15), Some(origin), eastern());

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

    /// 90m does not divide eastern()'s -4h offset, so the grid only lands on local 09:00 if it is
    /// anchored at local midnight. A UTC-anchored grid gives 09:30.
    #[test]
    fn grid_is_anchored_at_local_midnight() {
        let mut agg = CandleAggregator::new(SignedDuration::from_mins(90), None, eastern());

        agg.update(&at((2025, 6, 10), (10, 0, 0), "1", 1));

        assert_eq!(
            agg.candle().unwrap().timestamp(),
            at((2025, 6, 10), (9, 0, 0), "0", 0).timestamp()
        );
    }

    /// The grid follows local 18:00 across DST; a UTC-anchored grid would drift by an hour.
    #[test]
    fn origin_holds_local_time_across_dst() {
        let origin = time(18, 0, 0, 0);

        for date in [(2025, 1, 10), (2025, 6, 10)] {
            let mut agg =
                CandleAggregator::new(SignedDuration::from_mins(15), Some(origin), eastern());
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
        let origin = time(18, 0, 0, 0);
        let mut agg = CandleAggregator::new(SignedDuration::from_mins(15), Some(origin), eastern());

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
        let origin = time(18, 0, 0, 0);

        for date in [(2008, 3, 8), (2008, 3, 9)] {
            let mut agg =
                CandleAggregator::new(SignedDuration::from_mins(90), Some(origin), eastern());
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
        let origin = time(18, 0, 0, 0);
        let mut agg = CandleAggregator::new(SignedDuration::from_mins(15), Some(origin), eastern());

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
        let mut agg = CandleAggregator::new(SignedDuration::from_mins(15), None, eastern());

        agg.update(&at((2025, 6, 10), (10, 16, 0), "1", 1));
        agg.update(&at((2025, 6, 10), (10, 5, 0), "2", 1));
    }

    // --- Sessions ---

    /// An overnight session opening 18:00 belongs to the *next* trading day.
    #[test]
    fn overnight_key_rolls_to_next_day() {
        let mut agg = SessionAggregator::new(time(18, 0, 0, 0), time(17, 0, 0, 0), eastern());
        assert_eq!(agg.session_type(), SessionType::Overnight);

        agg.update(&at((2025, 6, 8), (18, 30, 0), "1", 1));
        assert_eq!(agg.current_key(), Some(date(2025, 6, 9)));

        // Monday morning is the same session.
        assert!(agg.update(&at((2025, 6, 9), (9, 30, 0), "2", 1)).is_none());
        assert_eq!(agg.current_key(), Some(date(2025, 6, 9)));
    }

    /// The emitted daily bar is stamped at the session open, not at its first record.
    #[test]
    fn session_bar_is_stamped_at_session_open() {
        let mut agg = SessionAggregator::new(time(18, 0, 0, 0), time(17, 0, 0, 0), eastern());

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
        let mut agg = SessionAggregator::new(time(9, 30, 0, 0), time(16, 0, 0, 0), eastern());
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
        let mut week = WeekAggregator::new(eastern());
        let sunday = at((2025, 6, 8), (18, 0, 0), "1", 1);
        let friday = at((2025, 6, 13), (18, 0, 0), "2", 1);

        assert!(week.update(&sunday).is_none());
        assert_eq!(week.current_week_start(), Some(date(2025, 6, 8)));
        assert!(week.update(&friday).is_none());
        assert_eq!(week.current_week_start(), Some(date(2025, 6, 8)));

        let next_sunday = at((2025, 6, 15), (18, 0, 0), "3", 1);
        let completed = week.update(&next_sunday).expect("new week");
        assert_eq!(completed.open(), p("1"));
        assert_eq!(completed.close(), p("2"));
    }

    mod preserve_behavior {
        use super::*;

        #[test]
        fn merges_ohlcv_within_a_bucket() {
            let mut agg = CandleAggregator::new(SignedDuration::from_mins(15), None, eastern());
            let base = at((2025, 6, 10), (10, 0, 0), "0", 0).timestamp();

            agg.update(&ohlc(base, "10", "12", "9", "11", 5));
            agg.update(&ohlc(
                base + SignedDuration::from_mins(1),
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
            assert_eq!(completed.volume(), Volume::from_units(12));
        }

        #[test]
        fn first_record_emits_nothing() {
            let mut agg = CandleAggregator::new(SignedDuration::from_mins(15), None, eastern());

            assert!(agg.update(&at((2025, 6, 10), (10, 0, 0), "1", 1)).is_none());
        }

        #[test]
        fn flush_emits_the_open_bucket() {
            let mut agg = CandleAggregator::new(SignedDuration::from_mins(15), None, eastern());
            agg.update(&at((2025, 6, 10), (10, 0, 0), "1", 3));

            let flushed = agg.flush().expect("in-progress bar");
            assert_eq!(flushed.volume(), Volume::from_units(3));
            assert!(agg.flush().is_none());
        }

        #[test]
        fn session_chains_into_week() {
            let mut session =
                SessionAggregator::new(time(18, 0, 0, 0), time(17, 0, 0, 0), eastern());
            let mut week = WeekAggregator::new(eastern());

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
            assert_eq!(week.candle().unwrap().volume(), Volume::from_units(2));
        }
    }
}
