use chrono::{NaiveDate, Weekday};
use instrid::prelude::FuturesContract;

use super::{DateOffset, EndOfTrading, NthInMonth, nth_weekday_of_month};

/// "Nth weekday of the contract month, then offset."
///
/// Used by most index, FX, and crypto futures whose Last Trading Day is
/// defined relative to a weekday within the contract month (e.g. ES, NQ, FDAX,
/// NKD: *third Friday*; BTC, ETH, MET: *last Friday*; SIX_E, SIX_B, SIX_A,
/// SIX_C: *third Wednesday*).
///
/// The `offset` typically encodes both a defensive `-1 business day` (to avoid
/// the actual termination day, where regular trading hours may not apply) and
/// any spec-defined additional offset (e.g. "2 business days prior to the
/// third Wednesday" → `-3 business days` total).
#[derive(Debug, Clone, Copy)]
pub struct NthWeekdayOfCurrentMonth {
    pub n: NthInMonth,
    pub weekday: Weekday,
    pub offset: DateOffset,
}

impl EndOfTrading for NthWeekdayOfCurrentMonth {
    fn calculate(&self, contract: &FuturesContract) -> NaiveDate {
        let date = nth_weekday_of_month(
            contract.year() as i32,
            contract.tenor().ordinal() as u32,
            self.weekday,
            self.n,
        );
        self.offset.apply(date)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use instrid::prelude::{Asset, AssetClass, Mic, Tenor};

    fn es(year: u16, tenor: Tenor) -> FuturesContract {
        FuturesContract::new(
            Asset::new("ES", AssetClass::Index),
            Asset::new("USD", AssetClass::Currency),
            Mic::xcme(),
            year,
            tenor,
            None,
        )
    }

    #[test]
    fn es_dec_2025_third_friday_minus_1_bday() {
        // Spec: ES terminates on the 3rd Friday of the contract month.
        // We add -1 BDay defensive offset.
        // Dec 2025: 3rd Friday = Dec 19 (Fri). -1 BDay = Dec 18 (Thu).
        let rule = NthWeekdayOfCurrentMonth {
            n: NthInMonth::Third,
            weekday: Weekday::Fri,
            offset: DateOffset::BusinessDays(-1),
        };
        assert_eq!(
            rule.calculate(&es(2025, Tenor::December)),
            NaiveDate::from_ymd_opt(2025, 12, 18).unwrap()
        );
    }

    #[test]
    fn es_mar_2026_third_friday_minus_1_bday() {
        // Mar 2026: 3rd Friday = Mar 20 (Fri). -1 BDay = Mar 19 (Thu).
        let rule = NthWeekdayOfCurrentMonth {
            n: NthInMonth::Third,
            weekday: Weekday::Fri,
            offset: DateOffset::BusinessDays(-1),
        };
        assert_eq!(
            rule.calculate(&es(2026, Tenor::March)),
            NaiveDate::from_ymd_opt(2026, 3, 19).unwrap()
        );
    }

    #[test]
    fn btc_last_friday_dec_2025() {
        // BTC: last Friday of the contract month. Dec 2025: last Friday = Dec 26 (Fri).
        // -1 BDay = Dec 25 (Thu) — we don't model the Christmas holiday.
        let rule = NthWeekdayOfCurrentMonth {
            n: NthInMonth::Last,
            weekday: Weekday::Fri,
            offset: DateOffset::BusinessDays(-1),
        };
        assert_eq!(
            rule.calculate(&es(2025, Tenor::December)),
            NaiveDate::from_ymd_opt(2025, 12, 25).unwrap()
        );
    }

    #[test]
    fn six_e_third_wednesday_minus_3_bdays() {
        // 6E (Euro FX): 2 BDay prior to 3rd Wednesday, + (-1) defensive = -3 BDay total.
        // Mar 2026: 3rd Wednesday = Mar 18 (Wed). -3 BDay = Mar 13 (Fri).
        let rule = NthWeekdayOfCurrentMonth {
            n: NthInMonth::Third,
            weekday: Weekday::Wed,
            offset: DateOffset::BusinessDays(-3),
        };
        assert_eq!(
            rule.calculate(&es(2026, Tenor::March)),
            NaiveDate::from_ymd_opt(2026, 3, 13).unwrap()
        );
    }

    #[test]
    fn no_offset() {
        // Sanity: zero offset returns the raw nth-weekday.
        let rule = NthWeekdayOfCurrentMonth {
            n: NthInMonth::Third,
            weekday: Weekday::Fri,
            offset: DateOffset::BusinessDays(0),
        };
        assert_eq!(
            rule.calculate(&es(2025, Tenor::December)),
            NaiveDate::from_ymd_opt(2025, 12, 19).unwrap()
        );
    }
}
