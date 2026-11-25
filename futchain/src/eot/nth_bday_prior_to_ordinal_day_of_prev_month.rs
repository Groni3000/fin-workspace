use std::num::NonZeroU8;

use instrid::prelude::FuturesContract;
use jiff::{ToSpan, civil::Date};

use super::{DateOffset, EndOfTrading, add_business_days, is_weekend, month_start};

/// "N business days prior to the Mth calendar day of the month *preceding*
/// the contract month, then offset."
#[derive(Debug, Clone, Copy)]
pub struct NthBDayPriorToOrdinalDayOfPrevMonth {
    pub ordinal_day: u8,
    pub n: NonZeroU8,
    pub offset: DateOffset,
}

impl NthBDayPriorToOrdinalDayOfPrevMonth {
    pub const fn new(ordinal_day: u8, n: NonZeroU8, offset: DateOffset) -> Self {
        Self {
            ordinal_day,
            n,
            offset,
        }
    }

    pub const fn from_u8(ordinal_day: u8, n: u8, offset: DateOffset) -> Self {
        let n = match NonZeroU8::new(n) {
            Some(nz) => nz,
            None => panic!("n must be non-zero"),
        };
        Self {
            ordinal_day,
            n,
            offset,
        }
    }
}

impl EndOfTrading for NthBDayPriorToOrdinalDayOfPrevMonth {
    fn calculate(&self, contract: &FuturesContract) -> Date {
        let prev_month = month_start(contract) - 1.month();
        let anchor = i8::try_from(self.ordinal_day)
            .ok()
            .and_then(|day| prev_month.with().day(day).build().ok())
            .expect("invariant: ordinal_day must be valid for the prior month");
        let mut walk = -(self.n.get() as i32);
        if is_weekend(anchor) {
            walk -= 1;
        }
        self.offset.apply(add_business_days(anchor, walk))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use instrid::{
        mic::Mic,
        prelude::{Asset, AssetClass, Tenor},
    };
    use jiff::civil::date;
    use tradeprim::currency::Currency;

    // https://www.cmegroup.com/markets/energy/crude-oil/light-sweet-crude.contractSpecs.html
    // FND = EOT + 2 BDay => EOT - 3 business day before
    // the 25th calendar day of the month prior to the contract month
    fn cl(year: u16, tenor: Tenor) -> FuturesContract {
        FuturesContract::new_unchecked(
            Asset::new("CL", AssetClass::Commodity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnym(),
            Currency::usd().into(),
            year,
            tenor,
            None,
        )
    }

    #[test]
    fn apr_2026_anchors_on_mar_25() {
        // Apr 2026 contract → anchor Mar 25 2026 (Wed). -3 BDays = Fri Mar 20.
        let rule = NthBDayPriorToOrdinalDayOfPrevMonth::from_u8(25, 3, DateOffset::BusinessDays(0));
        assert_eq!(rule.calculate(&cl(2026, Tenor::April)), date(2026, 3, 20));
    }

    #[test]
    fn jan_contract_wraps_into_previous_year() {
        // Jan 2026 contract → anchor Dec 25 2025 (Thu).
        // -3 BDays: Wed 24, Tue 23, Mon Dec 22.
        let rule = NthBDayPriorToOrdinalDayOfPrevMonth::from_u8(25, 3, DateOffset::BusinessDays(0));
        assert_eq!(
            rule.calculate(&cl(2026, Tenor::January)),
            date(2025, 12, 22)
        );
    }

    #[test]
    fn weekend_anchor_extends_walk() {
        // May 2026 contract → anchor Apr 25 2026 (Sat) → walk = -4.
        // From Sat: Fri 24, Thu 23, Wed 22, Tue Apr 21.
        let rule = NthBDayPriorToOrdinalDayOfPrevMonth::from_u8(25, 3, DateOffset::BusinessDays(0));
        assert_eq!(rule.calculate(&cl(2026, Tenor::May)), date(2026, 4, 21));
    }
}
