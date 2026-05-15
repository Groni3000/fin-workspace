use std::num::NonZeroU8;

use chrono::NaiveDate;
use instrid::prelude::FuturesContract;

use super::{DateOffset, EndOfTrading, add_business_days, month_start};

/// "The Nth-from-last business day of the month *preceding* the contract
/// month, then offset."
///
/// `n = 1` means the last business day of the prior month, `n = 2` means the
/// second-to-last, and so on. Mirrors the venue spec language for products
/// like NG (`n = 3`), GC, HG, ZS, RB, HO, SI, SB, ZW (all `n = 1`).
///
/// Note: this is *prior month*, not contract month. NG March contract's EOT
/// is computed from February's calendar.
///
/// Implementation: take the first day of the contract month and walk back `n`
/// business days. Then apply `offset` (usually `-1 business day` defensive).
#[derive(Debug, Clone, Copy)]
pub struct LastNthBDayOfPrevMonth {
    pub n: NonZeroU8,
    pub offset: DateOffset,
}

impl LastNthBDayOfPrevMonth {
    /// Construct from a typed [`NonZeroU8`]. Use this when `n` comes from
    /// runtime input — pair with `NonZeroU8::new(n).ok_or(...)` to keep the
    /// zero-rejection in your error type.
    pub const fn new(n: NonZeroU8, offset: DateOffset) -> Self {
        Self { n, offset }
    }

    /// Ergonomic constructor for literal `n` (the common case in product
    /// catalogues). **Panics** if `n == 0`; in `const` context the panic
    /// becomes a compile error.
    pub const fn from_u8(n: u8, offset: DateOffset) -> Self {
        let n = match NonZeroU8::new(n) {
            Some(nz) => nz,
            None => panic!("n must be non-zero"),
        };
        Self { n, offset }
    }
}

impl EndOfTrading for LastNthBDayOfPrevMonth {
    fn calculate(&self, contract: &FuturesContract) -> NaiveDate {
        let start = month_start(contract.year() as i32, contract.tenor().ordinal() as u32);
        let date = add_business_days(start, -(self.n.get() as i32));
        self.offset.apply(date)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use instrid::prelude::{Asset, AssetClass, Mic, Tenor};

    fn gc(year: u16, tenor: Tenor) -> FuturesContract {
        FuturesContract::new(
            Asset::new("GC", AssetClass::Commodity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnym(),
            year,
            tenor,
            None,
        )
    }

    #[test]
    fn gc_feb_2026_last_bday_minus_1() {
        // Spec: GC uses FND = last business day of previous month.
        // Feb 2026 contract → last bday of Jan 2026 = Jan 30 (Fri).
        // -1 BDay defensive offset → Jan 29 (Thu).
        let rule = LastNthBDayOfPrevMonth::from_u8(1, DateOffset::BusinessDays(-1));
        assert_eq!(
            rule.calculate(&gc(2026, Tenor::February)),
            NaiveDate::from_ymd_opt(2026, 1, 29).unwrap()
        );
    }

    #[test]
    fn gc_apr_2026_last_bday_minus_1() {
        // Apr 2026: month_start = Apr 1 (Wed). -1 BDay = Mar 31 (Tue).
        // -1 BDay defensive offset → Mar 30 (Mon).
        let rule = LastNthBDayOfPrevMonth::from_u8(1, DateOffset::BusinessDays(-1));
        assert_eq!(
            rule.calculate(&gc(2026, Tenor::April)),
            NaiveDate::from_ymd_opt(2026, 3, 30).unwrap()
        );
    }

    #[test]
    fn ng_mar_2026_third_to_last_bday_minus_1() {
        // NG: n=3, offset=BDay(-1). Mar 2026 contract → 3rd-to-last bday of Feb.
        // Feb 2026 last 3 bdays: Feb 27, 26, 25. So 3rd-from-last = Feb 25 (Wed).
        // -1 BDay defensive → Feb 24 (Tue).
        let rule = LastNthBDayOfPrevMonth::from_u8(3, DateOffset::BusinessDays(-1));
        assert_eq!(
            rule.calculate(&gc(2026, Tenor::March)),
            NaiveDate::from_ymd_opt(2026, 2, 24).unwrap()
        );
    }

    #[test]
    fn jan_contract_walks_into_previous_year() {
        // Jan 2026 contract → last bday of Dec 2025 = Dec 31 (Wed).
        // -1 BDay defensive → Dec 30 (Tue).
        let rule = LastNthBDayOfPrevMonth::from_u8(1, DateOffset::BusinessDays(-1));
        assert_eq!(
            rule.calculate(&gc(2026, Tenor::January)),
            NaiveDate::from_ymd_opt(2025, 12, 30).unwrap()
        );
    }

    #[test]
    fn leap_year_february() {
        // Mar 2024 contract → last bday of Feb 2024 (leap year) = Feb 29 (Thu).
        // No offset, sanity check the leap-year boundary.
        let rule = LastNthBDayOfPrevMonth::from_u8(1, DateOffset::BusinessDays(0));
        assert_eq!(
            rule.calculate(&gc(2024, Tenor::March)),
            NaiveDate::from_ymd_opt(2024, 2, 29).unwrap()
        );
    }
}
