pub mod asset;
pub mod inline_str;
pub mod instruments;
pub mod mic;
pub mod spec;
pub mod tenor;

// TODO:
//  - serde deserializes Cow always using Owned arm...
//    It seems I need to write my visitors to get rid of allocations (for 2/3 cases).

/// Common imports for users of this crate.
///
/// ```
/// use instrid::prelude::*;
/// ```
pub mod prelude {
    pub use crate::asset::{Asset, AssetClass};
    pub use crate::instruments::{
        ExerciseStyle, FuturesContract, Instrument, OptionContract, OptionKind, Stock,
        TradedInstrument,
    };
    pub use crate::mic::{
        Date, MarketCategoryCode, Mic, MicIso, MicStatus, MicType, mic_by_code, mic_iso_by_code,
    };
    pub use crate::tenor::Tenor;
}

/// Used to check that `T` borrows nothing from
/// a deserializer input.
///
/// i.e. `T` does not hold any `&'de` reference-field.
///
/// **It says nothing about the process of deserialization.
/// It just checks resulting type.**
#[cfg(feature = "serde")]
pub(crate) fn _assert_owned<T: serde::de::DeserializeOwned>() {}

/// Days in `month` (1–12) for `year`. Returns 0 for an invalid month.
pub(crate) const fn days_in_month(year: u16, month: u8) -> u8 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 if year % 4 == 0 && (year % 100 != 0 || year % 400 == 0) => 29,
        2 => 28,
        _ => 0,
    }
}

#[cfg(test)]
mod calendar_tests {
    use super::days_in_month;
    use crate::prelude::*;
    use chrono::NaiveDate;
    use proptest::prelude::*;
    use tradeprim::currency::Currency;
    use tradeprim::price::Price;

    /// Get last day of the (year, month) using chrono to test against it
    fn chrono_days_in_month(year: u16, month: u8) -> u8 {
        (28..=31u32)
            .rev()
            .find(|d| NaiveDate::from_ymd_opt(year as i32, month as u32, *d).is_some())
            .expect("every valid month has 28..=31 days") as u8
    }

    fn option_with(year: u16, tenor: Tenor, day: u8) -> Option<OptionContract> {
        OptionContract::new(
            Asset::new("AAPL", AssetClass::Equity).unwrap(),
            Asset::new("USD", AssetClass::Currency).unwrap(),
            Mic::xnas(),
            Currency::usd(),
            year,
            tenor,
            day,
            OptionKind::Call,
            ExerciseStyle::American,
            Price::from_str_unchecked("200"),
        )
    }

    fn future_with(year: u16, tenor: Tenor, day: Option<u8>) -> Option<FuturesContract> {
        FuturesContract::new(
            Asset::new("CL", AssetClass::Commodity).unwrap(),
            Asset::new("USD", AssetClass::Currency).unwrap(),
            Mic::xnym(),
            Currency::usd(),
            year,
            tenor,
            day,
        )
    }

    #[test]
    fn days_in_month_known_values() {
        assert_eq!(days_in_month(2025, 1), 31);
        assert_eq!(days_in_month(2025, 2), 28, "2025 is not a leap year");
        assert_eq!(days_in_month(2024, 2), 29, "2024 is divisible by 4");
        assert_eq!(days_in_month(1900, 2), 28, "century, not divisible by 400");
        assert_eq!(days_in_month(2000, 2), 29, "divisible by 400");
        assert_eq!(days_in_month(2025, 4), 30);
        assert_eq!(days_in_month(2025, 12), 31);
    }

    #[test]
    fn days_in_month_rejects_invalid_month() {
        assert_eq!(days_in_month(2025, 0), 0);
        assert_eq!(days_in_month(2025, 13), 0);
        assert_eq!(days_in_month(2025, u8::MAX), 0);
    }

    proptest! {
        /// Our version to get number of days in (year, month) should follow chrono.
        #[test]
        fn days_in_month_matches_chrono(year in 0u16..=u16::MAX, month in 1u8..=12) {
            prop_assert_eq!(
                days_in_month(year, month),
                chrono_days_in_month(year, month),
                "year={} month={}", year, month
            );
        }

        /// `OptionContract::new` must accept exactly the (year, month, day).
        /// If date does not exist (by chrono), `OptionContract::new` must reject it with `None`.
        #[test]
        fn option_constructor_accepts_exactly_valid_dates(
            year in 0u16..=3000, month in 1u8..=12, day in 0u8..=40,
        ) {
            let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");
            let chrono_some =
                NaiveDate::from_ymd_opt(year as i32, month as u32, day as u32).is_some();
            prop_assert_eq!(
                option_with(year, tenor, day).is_some(), chrono_some,
                "year={} month={} day={}", year, month, day
            );
        }

        /// `FuturesContract::new` must accept exactly the (year, month, day).
        /// If date does not exist (by chrono), `FuturesContract::new` must reject it with `None`.
        #[test]
        fn future_constructor_accepts_exactly_valid_dates(
            year in 0u16..=3000, month in 1u8..=12, day in 0u8..=40,
        ) {
            let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");
            let chrono_ok =
                NaiveDate::from_ymd_opt(year as i32, month as u32, day as u32).is_some();
            prop_assert_eq!(
                future_with(year, tenor, Some(day)).is_some(), chrono_ok,
                "year={} month={} day={}", year, month, day
            );
            prop_assert!(
                future_with(year, tenor, None).is_some(),
                "day: None must always be accepted"
            );
        }

        /// Roundtrip test.
        /// `date -> OptionContract -> OptionContract.date == date`
        /// `date -> FuturesContract -> FuturesContract.date == date`
        #[test]
        fn accepted_day_is_preserved(year in 1u16..=3000, month in 1u8..=12, day in 1u8..=31) {
            let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");
            if let Some(opt) = option_with(year, tenor, day) {
                prop_assert_eq!(opt.day(), day);
                prop_assert_eq!(opt.year(), year);
                prop_assert_eq!(opt.tenor(), tenor);
            }
            if let Some(fut) = future_with(year, tenor, Some(day)) {
                prop_assert!(fut.day().is_some_and(|d| d == day));
                prop_assert_eq!(fut.year(), year);
                prop_assert_eq!(fut.tenor(), tenor);
            }
        }
    }

    #[test]
    fn common_constructors_rejects() {
        assert!(
            option_with(2025, Tenor::February, 0).is_none(),
            "day 0 is rejected"
        );
        assert!(
            option_with(2025, Tenor::February, 29).is_none(),
            "2025 is not a leap year"
        );
        assert!(option_with(2025, Tenor::April, 31).is_none());
        assert!(option_with(2025, Tenor::December, 32).is_none());
        assert!(future_with(2025, Tenor::February, Some(30)).is_none());
    }
}
