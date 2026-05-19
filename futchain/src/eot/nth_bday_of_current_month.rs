use std::num::NonZeroU8;

use chrono::NaiveDate;
use instrid::prelude::FuturesContract;

use super::{DateOffset, EndOfTrading, add_business_days, is_weekend, month_start};

/// "The Nth business day of the contract month, then offset."
///
/// `n = 1` means the first business day, `n = 2` the second, and so on.
///
/// **Month-start adjustment.** When `month_start` is itself a business day,
/// it counts as the first BDay — so we walk `n - 1` days forward. When
/// `month_start` falls on a weekend, the next BDay is already the first, and
/// we walk a full `n` days.
#[derive(Debug, Clone, Copy)]
pub struct NthBDayOfCurrentMonth {
    pub n: NonZeroU8,
    pub offset: DateOffset,
}

impl NthBDayOfCurrentMonth {
    pub const fn new(n: NonZeroU8, offset: DateOffset) -> Self {
        Self { n, offset }
    }

    pub const fn from_u8(n: u8, offset: DateOffset) -> Self {
        let n = match NonZeroU8::new(n) {
            Some(nz) => nz,
            None => panic!("n must be non-zero"),
        };
        Self { n, offset }
    }
}

impl EndOfTrading for NthBDayOfCurrentMonth {
    fn calculate(&self, contract: &FuturesContract) -> NaiveDate {
        let start = month_start(contract.year() as i32, contract.tenor().ordinal() as u32);
        let walk = if is_weekend(start) {
            self.n.get() as i32
        } else {
            (self.n.get() as i32) - 1
        };
        self.offset.apply(add_business_days(start, walk))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use instrid::prelude::{Asset, AssetClass, Mic, Tenor};

    /// HE@XCME - Lean Hogs. LTD is the 10th business day of the contract
    /// month with a -1 BDay defensive offset.
    fn he(year: u16, tenor: Tenor) -> FuturesContract {
        FuturesContract::new(
            Asset::new("HE", AssetClass::Commodity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xcme(),
            year,
            tenor,
            None,
        )
    }

    #[test]
    fn first_bday_jul_2026_starts_on_wednesday() {
        // Jul 1 2026 = Wed (BDay). n=1 → walk 0 → Jul 1.
        let rule = NthBDayOfCurrentMonth::from_u8(1, DateOffset::BusinessDays(0));
        assert_eq!(
            rule.calculate(&he(2026, Tenor::July)),
            NaiveDate::from_ymd_opt(2026, 7, 1).unwrap()
        );
    }

    #[test]
    fn first_bday_feb_2026_starts_on_sunday() {
        // Feb 1 2026 = Sun. n = 1 -> walk 1 → Mon Feb 2.
        let rule = NthBDayOfCurrentMonth::from_u8(1, DateOffset::BusinessDays(0));
        assert_eq!(
            rule.calculate(&he(2026, Tenor::February)),
            NaiveDate::from_ymd_opt(2026, 2, 2).unwrap()
        );
    }

    #[test]
    fn third_bday_feb_2026() {
        // Feb 2026: BDays start Mon Feb 2, Tue 3, Wed Feb 4 = 3rd.
        let rule = NthBDayOfCurrentMonth::from_u8(3, DateOffset::BusinessDays(0));
        assert_eq!(
            rule.calculate(&he(2026, Tenor::February)),
            NaiveDate::from_ymd_opt(2026, 2, 4).unwrap()
        );
    }

    #[test]
    fn second_bday_jul_2026() {
        // Jul 1 2026 = Wed (BDay). n=2 → walk 1 → Thu Jul 2.
        let rule = NthBDayOfCurrentMonth::from_u8(2, DateOffset::BusinessDays(0));
        assert_eq!(
            rule.calculate(&he(2026, Tenor::July)),
            NaiveDate::from_ymd_opt(2026, 7, 2).unwrap()
        );
    }
}
