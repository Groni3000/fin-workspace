use chrono::{DateTime, TimeDelta, Utc};

/// Fires once, on the first timestamp that falls inside `[start, start + tolerance]`.
///
/// Driven by the timestamps the caller feeds it (usually event timestamps), so it
/// is **not** a timer: if no timestamp lands inside the window (a data gap, a halt,
/// or a tolerance shorter than the bar interval), it never fires and says nothing.
/// Good for "do X on the first bar after 15:55"; not for "do X at 15:55 no matter what".
#[derive(Debug)]
pub struct DateTimeTrigger {
    fired: bool,
    start_datetime: DateTime<Utc>,
    end_datetime: DateTime<Utc>,
}

impl DateTimeTrigger {
    pub fn new(start_datetime: DateTime<Utc>, tolerance: TimeDelta) -> Self {
        debug_assert!(tolerance.num_nanoseconds() > Some(0));
        Self {
            fired: false,
            start_datetime,
            end_datetime: start_datetime + tolerance,
        }
    }

    pub fn check_nanos(&mut self, ts: i64) -> bool {
        self.check_dt(DateTime::from_timestamp_nanos(ts))
    }

    pub fn check_dt(&mut self, ts: DateTime<Utc>) -> bool {
        if self.fired {
            return false;
        }
        if ts >= self.start_datetime && ts <= self.end_datetime {
            self.fired = true;
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn at(secs: i64) -> DateTime<Utc> {
        DateTime::from_timestamp(secs, 0).unwrap()
    }

    fn trigger() -> DateTimeTrigger {
        DateTimeTrigger::new(at(100), TimeDelta::seconds(10))
    }

    #[test]
    fn fires_once_inside_the_window() {
        let mut t = trigger();
        assert!(!t.check_dt(at(99)));
        assert!(t.check_dt(at(105)));
        assert!(!t.check_dt(at(106)), "only once");
    }

    #[test]
    fn both_ends_of_the_window_are_inclusive() {
        assert!(trigger().check_dt(at(100)));
        assert!(trigger().check_dt(at(110)));
    }

    #[test]
    fn never_fires_if_nothing_lands_in_the_window() {
        let mut t = trigger();
        assert!(!t.check_dt(at(90)));
        assert!(!t.check_dt(at(111)), "jumped over the window");
    }

    #[test]
    fn check_nanos_uses_the_same_window_to_the_nanosecond() {
        assert!(!trigger().check_nanos(99_999_999_999), "1ns before start");
        assert!(trigger().check_nanos(100_000_000_000), "start");
        assert!(trigger().check_nanos(110_000_000_000), "end");
        assert!(!trigger().check_nanos(110_000_000_001), "1ns after end");
    }

    #[test]
    fn check_nanos_and_check_dt_share_the_fired_state() {
        let mut t = trigger();
        assert!(t.check_nanos(105_000_000_000));
        assert!(!t.check_dt(at(105)), "already fired via nanos");
    }
}
