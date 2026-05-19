use chrono::{Duration, NaiveDate};
use instrid::prelude::FuturesContract;

use super::{DateOffset, EndOfTrading, add_business_days, is_weekend, month_start};

/// How to adjust a calendar date that lands on a non-business day.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NonBusinessDayAdjust {
    /// Roll back to the prior business day.
    Preceding,
    /// Roll forward to the next business day.
    Succeeding,
}

/// "The Nth calendar day of the contract month, adjusted off weekends per
/// `mode`, then offset."
///
/// Used by venue rules that specify a fixed day-of-month (e.g. "the 15th")
/// for the LTD, with a business-day convention for when that day lands on a
/// weekend.
#[derive(Debug, Clone, Copy)]
pub struct NthCalendarDayOfCurrentMonth {
    pub n: u8,
    pub mode: NonBusinessDayAdjust,
    pub offset: DateOffset,
}

impl EndOfTrading for NthCalendarDayOfCurrentMonth {
    fn calculate(&self, contract: &FuturesContract) -> NaiveDate {
        let start = month_start(contract.year() as i32, contract.tenor().ordinal() as u32);
        let mut date = start + Duration::days((self.n as i64) - 1);
        if is_weekend(date) {
            date = match self.mode {
                NonBusinessDayAdjust::Preceding => add_business_days(date, -1),
                NonBusinessDayAdjust::Succeeding => add_business_days(date, 1),
            };
        }
        self.offset.apply(date)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use instrid::prelude::{Asset, AssetClass, Mic, Tenor};

    /// https://www.eurex.com/ex-en/markets/int/fix/government-bonds/Euro-Bund-Futures-137298
    /// FGBL@XEUR is 8.5 to 10.5 years to maturity bonds with coupon of 6% yield.
    ///
    /// Delivery day: 10th calendar day of the contract month
    /// Last trading day: 2 business days before delivery day
    /// Succeeding mode
    fn fgbl(year: u16, tenor: Tenor) -> FuturesContract {
        FuturesContract::new(
            Asset::new("FGBL", AssetClass::FixedIncome).expect("Asset got incorrect parameters"),
            Asset::new("EUR", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xeur(),
            year,
            tenor,
            None,
        )
    }

    #[test]
    fn fifteenth_mar_2026_preceding() {
        // Mar 15 2026 = Sun. Preceding → Fri Mar 13.
        let rule = NthCalendarDayOfCurrentMonth {
            n: 15,
            mode: NonBusinessDayAdjust::Preceding,
            offset: DateOffset::BusinessDays(0),
        };
        assert_eq!(
            rule.calculate(&fgbl(2026, Tenor::March)),
            NaiveDate::from_ymd_opt(2026, 3, 13).unwrap()
        );
    }

    #[test]
    fn fifteenth_mar_2026_succeeding() {
        // Mar 15 2026 = Sun. Succeeding → Mon Mar 16.
        let rule = NthCalendarDayOfCurrentMonth {
            n: 15,
            mode: NonBusinessDayAdjust::Succeeding,
            offset: DateOffset::BusinessDays(0),
        };
        assert_eq!(
            rule.calculate(&fgbl(2026, Tenor::March)),
            NaiveDate::from_ymd_opt(2026, 3, 16).unwrap()
        );
    }

    #[test]
    fn weekday_anchor_is_unchanged() {
        // Jun 15 2026 = Mon. No adjustment regardless of mode.
        let rule = NthCalendarDayOfCurrentMonth {
            n: 15,
            mode: NonBusinessDayAdjust::Preceding,
            offset: DateOffset::BusinessDays(0),
        };
        assert_eq!(
            rule.calculate(&fgbl(2026, Tenor::June)),
            NaiveDate::from_ymd_opt(2026, 6, 15).unwrap()
        );
    }

    #[test]
    fn with_offset() {
        // Mar 15 2026 Sun → Preceding = Fri Mar 13; -1 BDay = Thu Mar 12.
        let rule = NthCalendarDayOfCurrentMonth {
            n: 15,
            mode: NonBusinessDayAdjust::Preceding,
            offset: DateOffset::BusinessDays(-1),
        };
        assert_eq!(
            rule.calculate(&fgbl(2026, Tenor::March)),
            NaiveDate::from_ymd_opt(2026, 3, 12).unwrap()
        );
    }
}
