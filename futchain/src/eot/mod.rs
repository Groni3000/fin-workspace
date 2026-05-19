use chrono::{Datelike, Duration, NaiveDate, Weekday};
use instrid::prelude::FuturesContract;

pub mod last_nth_bday_of_prev_month;
pub mod nth_bday_of_current_month;
pub mod nth_bday_prior_to_ordinal_day_of_prev_month;
pub mod nth_calendar_day_of_current_month;
pub mod nth_weekday_of_current_month;
pub mod nth_weekday_of_next_month;
pub use last_nth_bday_of_prev_month::LastNthBDayOfPrevMonth;
pub use nth_bday_of_current_month::NthBDayOfCurrentMonth;
pub use nth_bday_prior_to_ordinal_day_of_prev_month::NthBDayPriorToOrdinalDayOfPrevMonth;
pub use nth_calendar_day_of_current_month::{NonBusinessDayAdjust, NthCalendarDayOfCurrentMonth};
pub use nth_weekday_of_current_month::NthWeekdayOfCurrentMonth;
pub use nth_weekday_of_next_month::NthWeekdayOfNextMonth;

/// Computes the *end-of-trading* date for a given futures contract.
///
/// Implementors hold the *parameters* of the rule (e.g. "third Friday of the
/// contract month, offset by -1 business day"); the contract supplies the
/// (year, tenor) the rule resolves against. The returned [`NaiveDate`] is the
/// last day on which the contract should be considered tradable for rolling
/// purposes — usually a venue's Last Trading Day or First Notice Day, whichever
/// the user picked at construction time, plus a defensive business-day offset.
///
/// Rules are stateless with respect to the contract: one rule instance applies
/// to every contract in a chain, so reuse is free.
pub trait EndOfTrading {
    fn calculate(&self, contract: &FuturesContract) -> NaiveDate;
}

/// Which occurrence of a weekday within a month.
///
/// "Last" handles the cases where a month has 4 *or* 5 of the chosen weekday
/// (depending on the month's start day) — use it when you want "the final
/// Friday of the month" regardless of which ordinal it falls on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NthInMonth {
    First,
    Second,
    Third,
    Fourth,
    Last,
}

/// Offset applied after the rule's primary date has been computed.
///
/// Most venue rules want a small defensive shift (e.g. `-1` business day to
/// avoid trading on the actual termination day, where regular hours may not
/// apply). Calendar-day offsets exist for rules like VX whose spec literally
/// counts calendar days.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DateOffset {
    Days(i32),
    BusinessDays(i32),
}

impl DateOffset {
    pub fn apply(self, date: NaiveDate) -> NaiveDate {
        match self {
            DateOffset::Days(n) => date + Duration::days(n as i64),
            DateOffset::BusinessDays(n) => add_business_days(date, n),
        }
    }
}

/// Add `n` business days (skipping weekends only — no holiday calendar).
/// Negative `n` walks backwards.
pub(crate) fn add_business_days(date: NaiveDate, n: i32) -> NaiveDate {
    if n == 0 {
        return date;
    }
    let step = if n > 0 { 1 } else { -1 };
    let mut remaining = n.abs();
    let mut current = date;
    while remaining > 0 {
        current += Duration::days(step);
        if !is_weekend(current) {
            remaining -= 1;
        }
    }
    current
}

pub(crate) fn is_weekend(date: NaiveDate) -> bool {
    matches!(date.weekday(), Weekday::Sat | Weekday::Sun)
}

/// First day of the month containing `(year, month)`. Month is 1..=12.
pub(crate) fn month_start(year: i32, month: u32) -> NaiveDate {
    NaiveDate::from_ymd_opt(year, month, 1).expect("invariant: valid year/month")
}

/// Last day of the month containing `(year, month)`. Month is 1..=12.
pub(crate) fn month_end(year: i32, month: u32) -> NaiveDate {
    // First day of next month, minus one day.
    let (ny, nm) = if month == 12 {
        (year + 1, 1)
    } else {
        (year, month + 1)
    };
    NaiveDate::from_ymd_opt(ny, nm, 1).expect("invariant: valid year/month") - Duration::days(1)
}

/// Find the nth occurrence of `weekday` within the month containing
/// `(year, month)`. `Last` finds the final occurrence, regardless of whether
/// the month contains 4 or 5 of that weekday.
pub(crate) fn nth_weekday_of_month(
    year: i32,
    month: u32,
    weekday: Weekday,
    n: NthInMonth,
) -> NaiveDate {
    match n {
        NthInMonth::Last => {
            let end = month_end(year, month);
            let diff = (end.weekday().num_days_from_monday() as i32
                - weekday.num_days_from_monday() as i32)
                .rem_euclid(7);
            end - Duration::days(diff as i64)
        }
        first_to_fourth => {
            let ordinal = match first_to_fourth {
                NthInMonth::First => 0,
                NthInMonth::Second => 1,
                NthInMonth::Third => 2,
                NthInMonth::Fourth => 3,
                NthInMonth::Last => unreachable!(),
            };
            let start = month_start(year, month);
            let diff = (weekday.num_days_from_monday() as i32
                - start.weekday().num_days_from_monday() as i32)
                .rem_euclid(7);
            start + Duration::days((diff + 7 * ordinal) as i64)
        }
    }
}

#[cfg(test)]
mod helper_tests {
    use super::*;

    #[test]
    fn nth_weekday_third_friday_dec_2025() {
        // Dec 1, 2025 is Monday. Fridays: 5, 12, 19, 26. Third = 19.
        let d = nth_weekday_of_month(2025, 12, Weekday::Fri, NthInMonth::Third);
        assert_eq!(d, NaiveDate::from_ymd_opt(2025, 12, 19).unwrap());
    }

    #[test]
    fn nth_weekday_last_friday_dec_2025() {
        // Same month: last Friday = 26.
        let d = nth_weekday_of_month(2025, 12, Weekday::Fri, NthInMonth::Last);
        assert_eq!(d, NaiveDate::from_ymd_opt(2025, 12, 26).unwrap());
    }

    #[test]
    fn nth_weekday_first_monday_jan_2026() {
        // Jan 1, 2026 is Thursday. First Monday = Jan 5.
        let d = nth_weekday_of_month(2026, 1, Weekday::Mon, NthInMonth::First);
        assert_eq!(d, NaiveDate::from_ymd_opt(2026, 1, 5).unwrap());
    }

    #[test]
    fn nth_weekday_last_when_5_occurrences() {
        // May 2026 starts Friday. Fridays: 1, 8, 15, 22, 29. Last = 29.
        let d = nth_weekday_of_month(2026, 5, Weekday::Fri, NthInMonth::Last);
        assert_eq!(d, NaiveDate::from_ymd_opt(2026, 5, 29).unwrap());
    }

    #[test]
    fn add_business_days_minus_1_skips_weekend() {
        // Monday Dec 22, 2025. -1 BDay → Friday Dec 19.
        let mon = NaiveDate::from_ymd_opt(2025, 12, 22).unwrap();
        assert_eq!(
            add_business_days(mon, -1),
            NaiveDate::from_ymd_opt(2025, 12, 19).unwrap()
        );
    }

    #[test]
    fn add_business_days_plus_5_skips_weekend() {
        // Monday Dec 22, 2025 + 5 BDays → next Monday Dec 29.
        let mon = NaiveDate::from_ymd_opt(2025, 12, 22).unwrap();
        assert_eq!(
            add_business_days(mon, 5),
            NaiveDate::from_ymd_opt(2025, 12, 29).unwrap()
        );
    }

    #[test]
    fn add_business_days_zero_is_noop() {
        let d = NaiveDate::from_ymd_opt(2025, 12, 22).unwrap();
        assert_eq!(add_business_days(d, 0), d);
    }
}
