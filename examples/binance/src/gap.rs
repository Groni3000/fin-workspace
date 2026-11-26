//! Notices missing and repeated candles from their open times.

use jiff::{SignedDuration, Timestamp};

/// Candles that should have arrived between two that did: open times from `from` up to, not
/// including, `until`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Gap {
    pub from: Timestamp,
    pub until: Timestamp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Seen {
    /// The first candle, or the one right after the last.
    Next,
    /// A candle after a gap.
    AfterGap(Gap),
    /// An open time already seen or skipped over: the candle is to be dropped.
    Repeat,
}

/// Follows the open times of the closed candles of one instrument and interval.
#[derive(Debug, Clone)]
pub struct GapTracker {
    interval: SignedDuration,
    next: Option<Timestamp>,
}

impl GapTracker {
    pub fn new(interval: SignedDuration) -> Self {
        Self {
            interval,
            next: None,
        }
    }

    /// Where a candle opening at `open` falls. Only a candle that isn't a repeat moves the
    /// tracker on.
    pub fn see(&mut self, open: Timestamp) -> Seen {
        let seen = match self.next {
            Some(next) if open < next => return Seen::Repeat,
            Some(next) if open > next => Seen::AfterGap(Gap {
                from: next,
                until: open,
            }),
            _ => Seen::Next,
        };
        self.next = Some(open + self.interval);
        seen
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `s` seconds after 2026-11-26T01:46:05Z.
    fn t(s: i64) -> Timestamp {
        Timestamp::from_second(1_795_657_565 + s).unwrap()
    }

    fn tracker() -> GapTracker {
        GapTracker::new(SignedDuration::from_secs(1))
    }

    #[test]
    fn consecutive_candles_are_next() {
        let mut tracker = tracker();
        assert_eq!(
            [0, 1, 2].map(|s| tracker.see(t(s))),
            [Seen::Next, Seen::Next, Seen::Next]
        );
    }

    #[test]
    fn a_skipped_open_time_is_a_gap() {
        let mut tracker = tracker();
        tracker.see(t(0));
        assert_eq!(
            tracker.see(t(3)),
            Seen::AfterGap(Gap {
                from: t(1),
                until: t(3)
            })
        );
        assert_eq!(t(1).to_string(), "2026-11-26T01:46:06Z");
        assert_eq!(tracker.see(t(4)), Seen::Next);
    }

    #[test]
    fn a_repeat_does_not_move_the_tracker() {
        let mut tracker = tracker();
        tracker.see(t(0));
        tracker.see(t(1));
        assert_eq!(tracker.see(t(1)), Seen::Repeat);
        assert_eq!(tracker.see(t(0)), Seen::Repeat);
        assert_eq!(tracker.see(t(2)), Seen::Next);
    }

    /// The gap was reported already; a candle from inside it arriving late is dropped too.
    #[test]
    fn a_late_candle_from_a_gap_is_a_repeat() {
        let mut tracker = tracker();
        tracker.see(t(0));
        tracker.see(t(3));
        assert_eq!(tracker.see(t(2)), Seen::Repeat);
        assert_eq!(tracker.see(t(4)), Seen::Next);
    }
}
