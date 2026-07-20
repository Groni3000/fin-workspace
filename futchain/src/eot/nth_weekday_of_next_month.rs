use chrono::{NaiveDate, Weekday};
use instrid::prelude::FuturesContract;

use super::{DateOffset, EndOfTrading, NthInMonth, nth_weekday_of_month};

/// "Nth weekday of the month *following* the contract month, then offset."
///
/// Mirror of [`NthWeekdayOfCurrentMonth`] but for venue rules that anchor on
/// the month after the contract tenor.
///
/// **VX** (VIX@CBOE) - the most known futures that uses this rule.
/// VX settles 30 calendar days before the (SPX S&P 500 option expires)
/// third Friday of the month after the contract month —
/// i.e. this rule produces that third-Friday anchor,
/// and a `-30` calendar-day offset (composed by the caller) yields the
/// settlement Wednesday.
///
/// [`NthWeekdayOfCurrentMonth`]: super::NthWeekdayOfCurrentMonth
#[derive(Debug, Clone, Copy)]
pub struct NthWeekdayOfNextMonth {
    pub n: NthInMonth,
    pub weekday: Weekday,
    pub offset: DateOffset,
}

impl EndOfTrading for NthWeekdayOfNextMonth {
    fn calculate(&self, contract: &FuturesContract) -> NaiveDate {
        let year = contract.year() as i32;
        let month = contract.tenor().ordinal() as u32;
        let (ny, nm) = if month == 12 {
            (year + 1, 1)
        } else {
            (year, month + 1)
        };
        let date = nth_weekday_of_month(ny, nm, self.weekday, self.n);
        self.offset.apply(date)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use instrid::prelude::{Asset, AssetClass, Mic, Tenor};
    use tradeprim::currency::Currency;

    fn vx(year: u16, tenor: Tenor) -> FuturesContract {
        FuturesContract::new(
            Asset::new("VX", AssetClass::Index).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xcbo(),
            Currency::usd(),
            year,
            tenor,
            None,
        )
    }

    #[test]
    fn third_friday_next_month_dec_2025_contract() {
        // Dec 2025 contract → 3rd Friday of Jan 2026.
        // Jan 1 2026 = Thu. Fridays: 2, 9, 16, 23, 30. Third = Jan 16.
        let rule = NthWeekdayOfNextMonth {
            n: NthInMonth::Third,
            weekday: Weekday::Fri,
            offset: DateOffset::BusinessDays(0),
        };
        assert_eq!(
            rule.calculate(&vx(2025, Tenor::December)),
            NaiveDate::from_ymd_opt(2026, 1, 16).unwrap()
        );
    }

    #[test]
    fn last_wednesday_next_month_jan_2026() {
        // Jan 2026 contract → last Wednesday of Feb 2026.
        // Feb 1 2026 = Sun. Wednesdays: 4, 11, 18, 25. Last = Feb 25.
        let rule = NthWeekdayOfNextMonth {
            n: NthInMonth::Last,
            weekday: Weekday::Wed,
            offset: DateOffset::BusinessDays(0),
        };
        assert_eq!(
            rule.calculate(&vx(2026, Tenor::January)),
            NaiveDate::from_ymd_opt(2026, 2, 25).unwrap()
        );
    }

    #[test]
    fn third_wednesday_next_month_minus_2_bdays() {
        // Mar 2026 contract → 3rd Wed of Apr 2026, -2 BDay offset.
        // Apr 1 2026 = Wed. Wednesdays: 1, 8, 15, 22. Third = Apr 15 (Wed).
        // -2 BDay = Apr 13 (Mon).
        let rule = NthWeekdayOfNextMonth {
            n: NthInMonth::Third,
            weekday: Weekday::Wed,
            offset: DateOffset::BusinessDays(-2),
        };
        assert_eq!(
            rule.calculate(&vx(2026, Tenor::March)),
            NaiveDate::from_ymd_opt(2026, 4, 13).unwrap()
        );
    }
}
