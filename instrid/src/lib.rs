#![doc = include_str!("../README.md")]

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
        2 if year.is_multiple_of(4) && (!year.is_multiple_of(100) || year.is_multiple_of(400)) => {
            29
        }
        2 => 28,
        _ => 0,
    }
}

#[cfg(test)]
mod calendar_tests {
    use super::days_in_month;
    use crate::instruments::{InvalidContractDate, MAX_YEAR};
    use crate::prelude::*;
    use jiff::civil::Date;
    use proptest::prelude::*;
    use tradeprim::currency::Currency;
    use tradeprim::price::Price;

    /// Whether the date exists in the calendar, by jiff.
    fn is_real_date(year: u16, month: u8, day: u8) -> bool {
        Date::new(year as i16, month as i8, day as i8).is_ok()
    }

    /// Days in (year, month) by jiff.
    fn jiff_days_in_month(year: u16, month: u8) -> u8 {
        let first = Date::new(year as i16, month as i8, 1).expect("a valid year and month");
        first.days_in_month() as u8
    }

    fn option_with(
        year: u16,
        tenor: Tenor,
        day: u8,
    ) -> Result<OptionContract, InvalidContractDate> {
        OptionContract::new(
            Asset::new("AAPL", AssetClass::Equity).unwrap(),
            Asset::new("USD", AssetClass::Currency).unwrap(),
            Mic::xnas(),
            Currency::usd().into(),
            year,
            tenor,
            day,
            OptionKind::Call,
            ExerciseStyle::American,
            Price::from_str_unchecked("200"),
        )
    }

    fn future_with(
        year: u16,
        tenor: Tenor,
        day: Option<u8>,
    ) -> Result<FuturesContract, InvalidContractDate> {
        FuturesContract::new(
            Asset::new("CL", AssetClass::Commodity).unwrap(),
            Asset::new("USD", AssetClass::Currency).unwrap(),
            Mic::xnym(),
            Currency::usd().into(),
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
        /// Our version to get number of days in (year, month) should follow jiff.
        #[test]
        fn days_in_month_matches_jiff(year in 0u16..=MAX_YEAR, month in 1u8..=12) {
            prop_assert_eq!(
                days_in_month(year, month),
                jiff_days_in_month(year, month),
                "year={} month={}", year, month
            );
        }

        /// `OptionContract::new` must accept exactly the (year, month, day).
        /// If date does not exist (by jiff), `OptionContract::new` must reject it with `Err`.
        #[test]
        fn option_constructor_accepts_exactly_valid_dates(
            year in 0u16..=MAX_YEAR, month in 1u8..=12, day in 0u8..=40,
        ) {
            let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");
            prop_assert_eq!(
                option_with(year, tenor, day).is_ok(), is_real_date(year, month, day),
                "year={} month={} day={}", year, month, day
            );
        }

        /// `FuturesContract::new` must accept exactly the (year, month, day).
        /// If date does not exist (by jiff), `FuturesContract::new` must reject it with `Err`.
        #[test]
        fn future_constructor_accepts_exactly_valid_dates(
            year in 0u16..=MAX_YEAR, month in 1u8..=12, day in 0u8..=40,
        ) {
            let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");
            prop_assert_eq!(
                future_with(year, tenor, Some(day)).is_ok(), is_real_date(year, month, day),
                "year={} month={} day={}", year, month, day
            );
            prop_assert!(
                future_with(year, tenor, None).is_ok(),
                "day: None must always be accepted"
            );
        }

        /// Past `MAX_YEAR` nothing is a valid contract date, whatever the day.
        #[test]
        fn years_past_max_year_are_rejected(
            year in (MAX_YEAR + 1)..=u16::MAX, month in 1u8..=12, day in 1u8..=28,
        ) {
            let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");
            let rejected = InvalidContractDate { year, tenor, day: None };
            prop_assert_eq!(future_with(year, tenor, None), Err(rejected));
            prop_assert!(future_with(year, tenor, Some(day)).is_err());
            prop_assert!(option_with(year, tenor, day).is_err());
            let fut = future_with(MAX_YEAR, tenor, None).expect("MAX_YEAR is valid");
            prop_assert_eq!(fut.with_year(year), Err(rejected));
            prop_assert_eq!(fut.with_year_tenor(year, tenor), Err(rejected));
        }

        /// The rejection must name the date that was rejected, not just fail.
        #[test]
        fn rejection_reports_the_offending_date(
            year in 0u16..=3000, month in 1u8..=12, day in 0u8..=40,
        ) {
            let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");
            if let Err(e) = option_with(year, tenor, day) {
                prop_assert_eq!(
                    e,
                    InvalidContractDate { year, tenor, day: Some(day) }
                );
            }
            if let Err(e) = future_with(year, tenor, Some(day)) {
                prop_assert_eq!(
                    e,
                    InvalidContractDate { year, tenor, day: Some(day) }
                );
            }
        }

        /// Roundtrip test.
        /// `date -> OptionContract -> OptionContract.date == date`
        /// `date -> FuturesContract -> FuturesContract.date == date`
        #[test]
        fn accepted_day_is_preserved(year in 1u16..=3000, month in 1u8..=12, day in 1u8..=31) {
            let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");
            if let Ok(opt) = option_with(year, tenor, day) {
                prop_assert_eq!(opt.day(), day);
                prop_assert_eq!(opt.year(), year);
                prop_assert_eq!(opt.tenor(), tenor);
            }
            if let Ok(fut) = future_with(year, tenor, Some(day)) {
                prop_assert!(fut.day().is_some_and(|d| d == day));
                prop_assert_eq!(fut.year(), year);
                prop_assert_eq!(fut.tenor(), tenor);
            }
        }
    }

    /// Serde must emit Results
    #[cfg(feature = "serde")]
    mod serde_tests {
        use super::*;

        /// Just a helper builder
        fn option_json(year: u16, month: u8, day: u8) -> String {
            format!(
                r#"{{"base":{{"name":"AAPL","class":"Equity"}},
                     "price_quotation":{{"name":"USD","class":"Currency"}},
                     "mic":"XNAS","settlement":{{"name":"USD","class":"Currency"}},
                     "year":{year},"tenor":{month},"day":{day},
                     "kind":"Call","style":"American","strike":"200"}}"#
            )
        }

        /// Just a helper builder
        fn future_json(year: u16, month: u8, day: u8) -> String {
            format!(
                r#"{{"base":{{"name":"CL","class":"Commodity"}},
                     "price_quotation":{{"name":"USD","class":"Currency"}},
                     "mic":"XNYM","settlement":{{"name":"USD","class":"Currency"}},
                     "year":{year},"tenor":{month},"day":{day}}}"#
            )
        }

        #[test]
        fn known_invalid_dates_are_rejected() {
            for (y, m, d) in [(2025, 2, 31), (2025, 12, 0), (2025, 4, 31), (2025, 2, 29)] {
                assert!(
                    serde_json::from_str::<OptionContract>(&option_json(y, m, d)).is_err(),
                    "option {y}-{m}-{d} must not deserialize"
                );
                assert!(
                    serde_json::from_str::<FuturesContract>(&future_json(y, m, d)).is_err(),
                    "future {y}-{m}-{d} must not deserialize"
                );
            }
        }

        #[test]
        fn years_up_to_max_year_deserialize_and_later_ones_dont() {
            assert!(serde_json::from_str::<OptionContract>(&option_json(9999, 12, 31)).is_ok());
            assert!(serde_json::from_str::<FuturesContract>(&future_json(9999, 12, 31)).is_ok());
            assert!(serde_json::from_str::<OptionContract>(&option_json(10000, 1, 1)).is_err());
            assert!(serde_json::from_str::<FuturesContract>(&future_json(10000, 1, 1)).is_err());
        }

        /// The `Instrument` enum should validate date too.
        #[test]
        fn instrument_enum_inherits_validation() {
            let tagged = format!(
                r#"{{"type":"Futures",{}"#,
                future_json(2025, 12, 0).trim_start_matches('{')
            );
            assert!(
                serde_json::from_str::<Instrument>(&tagged).is_err(),
                "Instrument must not deserialize a day-0 futures contract"
            );
        }

        proptest! {
            /// We already tested that "what jiff accepts - our internal functions accepts".
            /// So this test just checks that nothing wrong happens during deserialization
            /// via serde generated functions and our manual trait implementation.
            #[test]
            fn deserialize_accepts_exactly_valid_dates(
                year in 1u16..=3000, month in 1u8..=12, day in 0u8..=40,
            ) {
                let real = super::is_real_date(year, month, day);
                prop_assert_eq!(
                    serde_json::from_str::<OptionContract>(&option_json(year, month, day)).is_ok(),
                    real,
                    "option {}-{}-{}", year, month, day
                );
                prop_assert_eq!(
                    serde_json::from_str::<FuturesContract>(&future_json(year, month, day)).is_ok(),
                    real,
                    "future {}-{}-{}", year, month, day
                );
            }

            /// Option/Futures -> str (serialize) -> Option/Futures (deserialize)
            #[test]
            fn valid_contracts_round_trip(
                year in 1u16..=3000, month in 1u8..=12, day in 1u8..=31,
            ) {
                let tenor = Tenor::try_from(month).expect("1..=12 is a valid tenor");

                if let Ok(opt) = option_with(year, tenor, day) {
                    let json = serde_json::to_string(&opt).expect("serializable");
                    let back: OptionContract =
                        serde_json::from_str(&json).expect("a valid contract must round-trip");
                    prop_assert_eq!(back, opt);
                }

                if let Ok(fut) = future_with(year, tenor, Some(day)) {
                    let json = serde_json::to_string(&fut).expect("serializable");
                    let back: FuturesContract =
                        serde_json::from_str(&json).expect("a valid contract must round-trip");
                    prop_assert_eq!(back, fut);
                }

                let no_day = future_with(year, tenor, None).expect("None day is always valid");
                let json = serde_json::to_string(&no_day).expect("serializable");
                let back: FuturesContract = serde_json::from_str(&json).expect("round-trips");
                prop_assert_eq!(back, no_day);
            }
        }
    }

    #[test]
    fn common_constructors_rejects() {
        assert!(
            option_with(2025, Tenor::February, 0).is_err(),
            "day 0 is rejected"
        );
        assert!(
            option_with(2025, Tenor::February, 29).is_err(),
            "2025 is not a leap year"
        );
        assert!(option_with(2025, Tenor::April, 31).is_err());
        assert!(option_with(2025, Tenor::December, 32).is_err());
        assert!(future_with(2025, Tenor::February, Some(30)).is_err());
    }

    #[test]
    fn rejection_error_displays_the_date() {
        let e = option_with(2025, Tenor::February, 31).unwrap_err();
        assert_eq!(e.to_string(), "invalid contract date: 2025-02-31");

        let e = future_with(2025, Tenor::February, Some(0)).unwrap_err();
        assert_eq!(e.to_string(), "invalid contract date: 2025-02-00");
    }
}
