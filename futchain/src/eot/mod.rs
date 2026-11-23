use instrid::prelude::FuturesContract;
use jiff::{
    ToSpan,
    civil::{Date, Weekday},
};

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
/// (year, tenor) the rule resolves against. The returned [`Date`] is the
/// last day on which the contract should be considered tradable for rolling
/// purposes — usually a venue's Last Trading Day or First Notice Day, whichever
/// the user picked at construction time, plus a defensive business-day offset.
///
/// Rules are stateless with respect to the contract: one rule instance applies
/// to every contract in a chain, so reuse is free.
pub trait EndOfTrading {
    fn calculate(&self, contract: &FuturesContract) -> Date;
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
    pub fn apply(self, date: Date) -> Date {
        match self {
            DateOffset::Days(n) => date + n.days(),
            DateOffset::BusinessDays(n) => add_business_days(date, n),
        }
    }
}

/// Add `n` business days (skipping weekends only — no holiday calendar).
/// Negative `n` walks backwards.
pub(crate) fn add_business_days(date: Date, n: i32) -> Date {
    if n == 0 {
        return date;
    }
    let step = if n > 0 { 1 } else { -1 };
    let mut remaining = n.abs();
    let mut current = date;
    while remaining > 0 {
        current += step.days();
        if !is_weekend(current) {
            remaining -= 1;
        }
    }
    current
}

pub(crate) fn is_weekend(date: Date) -> bool {
    matches!(date.weekday(), Weekday::Saturday | Weekday::Sunday)
}

/// First day of the contract month.
pub(crate) fn month_start(contract: &FuturesContract) -> Date {
    i16::try_from(contract.year())
        .ok()
        .and_then(|year| Date::new(year, contract.tenor().ordinal() as i8, 1).ok())
        .expect("contract years end at 9999")
}

/// The nth occurrence of `weekday` in the month of `month`. `Last` is the final one, whether the
/// month has 4 or 5 of that weekday.
pub(crate) fn nth_weekday_of_month(month: Date, weekday: Weekday, n: NthInMonth) -> Date {
    let nth = match n {
        NthInMonth::First => 1,
        NthInMonth::Second => 2,
        NthInMonth::Third => 3,
        NthInMonth::Fourth => 4,
        NthInMonth::Last => -1,
    };
    month
        .nth_weekday_of_month(nth, weekday)
        .expect("every month has at least 4 of each weekday")
}

#[cfg(test)]
mod helper_tests {
    use super::*;
    use jiff::civil::date;

    #[test]
    fn nth_weekday_third_friday_dec_2025() {
        // Dec 1, 2025 is Monday. Fridays: 5, 12, 19, 26. Third = 19.
        let d = nth_weekday_of_month(date(2025, 12, 1), Weekday::Friday, NthInMonth::Third);
        assert_eq!(d, date(2025, 12, 19));
    }

    #[test]
    fn nth_weekday_last_friday_dec_2025() {
        // Same month: last Friday = 26.
        let d = nth_weekday_of_month(date(2025, 12, 1), Weekday::Friday, NthInMonth::Last);
        assert_eq!(d, date(2025, 12, 26));
    }

    #[test]
    fn nth_weekday_first_monday_jan_2026() {
        // Jan 1, 2026 is Thursday. First Monday = Jan 5.
        let d = nth_weekday_of_month(date(2026, 1, 1), Weekday::Monday, NthInMonth::First);
        assert_eq!(d, date(2026, 1, 5));
    }

    #[test]
    fn nth_weekday_last_when_5_occurrences() {
        // May 2026 starts Friday. Fridays: 1, 8, 15, 22, 29. Last = 29.
        let d = nth_weekday_of_month(date(2026, 5, 1), Weekday::Friday, NthInMonth::Last);
        assert_eq!(d, date(2026, 5, 29));
    }

    #[test]
    fn nth_weekday_second_and_fourth_when_5_occurrences() {
        // May 2026: Fridays 1, 8, 15, 22, 29. The fourth is not the last.
        let may = date(2026, 5, 1);
        assert_eq!(
            nth_weekday_of_month(may, Weekday::Friday, NthInMonth::Second),
            date(2026, 5, 8)
        );
        assert_eq!(
            nth_weekday_of_month(may, Weekday::Friday, NthInMonth::Fourth),
            date(2026, 5, 22)
        );
    }

    #[test]
    fn add_business_days_minus_1_skips_weekend() {
        // Monday Dec 22, 2025. -1 BDay → Friday Dec 19.
        let mon = date(2025, 12, 22);
        assert_eq!(add_business_days(mon, -1), date(2025, 12, 19));
    }

    #[test]
    fn add_business_days_plus_5_skips_weekend() {
        // Monday Dec 22, 2025 + 5 BDays → next Monday Dec 29.
        let mon = date(2025, 12, 22);
        assert_eq!(add_business_days(mon, 5), date(2025, 12, 29));
    }

    #[test]
    fn add_business_days_zero_is_noop() {
        let d = date(2025, 12, 22);
        assert_eq!(add_business_days(d, 0), d);
    }
}
