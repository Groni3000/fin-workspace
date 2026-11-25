use std::{fmt::Display, ops::Add};

use tradeprim::price::Price;

use crate::asset::Asset;

/// Has fixed scale and max value.
///
/// Pretty similar to `QuoteNotional`.
///
/// `SettlementNotional` is usually a result of multiplication of `QuoteNotional` by `PointValue`,
/// in the [`Asset`] the instrument settles in.
///
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SettlementNotional {
    // value: i128 = 16 bytes. Align = 16 bytes.
    // `Asset` is 14 bytes => 16 + 14 + 2 (padding) = 32 bytes.
    value: i128,
    settlement: Asset,
}

impl SettlementNotional {
    pub const SCALE: i128 = Price::SCALE as i128;
    pub const PRECISION: i128 = 9;

    pub const ONE_RAW: i128 = Self::SCALE;
    pub const ZERO_RAW: i128 = 0_i128;
    pub const MAX_RAW: i128 = i128::MAX;
    /// It would be naturally used in `Self::new`
    /// and ignored in `Self::new_unchecked`, but...
    ///
    /// It seems to be a very rare problem.
    ///
    /// Regardless, what can happen?
    /// Debug: panic
    /// Release: negate i128::MIN will be identity mapping
    /// SettlementNotional(i128::MIN).neg() == SettlementNotional(i128::MIN)
    ///
    /// I don't know... We can get it only from raw
    /// `SettlementNotional::new(i128::MIN...)` it's just... Malicious?
    /// Do I really want to protect from such code?
    ///
    /// Used only in Add as a guard
    pub const MIN_RAW: i128 = -Self::MAX_RAW;
    pub const MAX_INTEGER_PART: i128 = Self::MAX_RAW / Self::SCALE;

    /// Construct a `SettlementNotional` from a raw value and the asset it is in.
    ///
    /// # Note
    ///
    /// `value == i128::MIN` can lead to problems described in `SettlementNotional::MIN_RAW`.
    pub const fn new(value: i128, settlement: Asset) -> Self {
        Self { value, settlement }
    }

    pub fn value(&self) -> i128 {
        self.value
    }

    pub fn settlement(&self) -> &Asset {
        &self.settlement
    }

    /// Prefer `checked_add` over `add` when settlement mismatch/overflow is expected to happen.
    pub fn checked_add(self, rhs: Self) -> Result<Self, SnAddError> {
        if self.settlement != rhs.settlement {
            return Err(SnAddError::SettlementMismatch(
                self.settlement,
                rhs.settlement,
            ));
        }
        if let Some(sum) = self.value.checked_add(rhs.value)
            // Because SettlementNotional::MIN_RAW != i128::MIN
            // and it is only reachable via malicious raw construction
            // or sum or two perfectly in range values
            && sum != i128::MIN
        {
            return Ok(SettlementNotional::new(sum, self.settlement));
        }

        Err(SnAddError::Overflow(self.value, rhs.value))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SnAddError {
    SettlementMismatch(Asset, Asset),
    Overflow(i128, i128),
}

impl std::error::Error for SnAddError {}

impl Display for SnAddError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SettlementMismatch(a, b) => {
                write!(f, "Settlement mismatch: {} != {}", a, b)
            }
            Self::Overflow(a, b) => {
                write!(f, "Overflow: {} + {}", a, b)
            }
        }
    }
}

impl Add for SettlementNotional {
    type Output = SettlementNotional;

    /// Perform checked add, panic on overflow or different settlements.
    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(rhs).unwrap_or_else(|e| panic!("{e}"))
    }
}

impl Display for SettlementNotional {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.value.is_negative() {
            write!(f, "-")?;
        }

        let abs = self.value.unsigned_abs();
        let mut fractional_part = abs % Self::SCALE as u128;

        write_grouped(f, abs / Self::SCALE as u128)?;
        if fractional_part == 0 {
            return write!(f, " ({})", self.settlement.name());
        }

        let mut pow = Self::PRECISION as usize;
        while fractional_part.is_multiple_of(10) {
            fractional_part /= 10;
            pow -= 1;
        }
        write!(f, ".{:0pow$} ({})", fractional_part, self.settlement.name())
    }
}

/// Writes an integer with `_`-separated triples (e.g. `3000000` -> `3_000_000`).
fn write_grouped(f: &mut std::fmt::Formatter<'_>, value: u128) -> std::fmt::Result {
    if value >= 1000 {
        write_grouped(f, value / 1000)?;
        write!(f, "_{:03}", value % 1000)
    } else {
        write!(f, "{value}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tradeprim::currency::Currency;

    // helper
    fn usd() -> SettlementNotional {
        SettlementNotional::new(0, Currency::usd().into())
    }

    // helper that uses helper
    fn usd_raw(raw: i128) -> SettlementNotional {
        SettlementNotional::new(raw, usd().settlement)
    }

    fn eur_raw(raw: i128) -> SettlementNotional {
        SettlementNotional::new(raw, Currency::eur().into())
    }

    fn usdt_raw(raw: i128) -> SettlementNotional {
        SettlementNotional::new(raw, Asset::crypto("USDT").expect("valid name"))
    }

    #[test]
    fn display_half_dollar_fraction() {
        assert_eq!(usd_raw(552_812_500_000_000).to_string(), "552_812.5 (USD)");
    }

    #[test]
    fn display_leading_zero_fraction() {
        assert_eq!(usd_raw(50_000_000).to_string(), "0.05 (USD)");
    }

    #[test]
    fn display_smallest_fraction() {
        assert_eq!(usd_raw(1).to_string(), "0.000000001 (USD)");
    }

    #[test]
    fn display_zero_fraction_has_no_dot() {
        assert_eq!(usd_raw(552_812_000_000_000).to_string(), "552_812 (USD)");
    }

    #[test]
    fn display_zero() {
        assert_eq!(usd_raw(0).to_string(), "0 (USD)");
    }

    #[test]
    fn display_negative() {
        assert_eq!(usd_raw(-100_050_000_000).to_string(), "-100.05 (USD)");
    }

    #[test]
    fn add_same_currency_sums_and_keeps_tag() {
        // 100.05 + 50.20 = 150.25, still USD.
        let sum = usd_raw(100_050_000_000) + usd_raw(50_200_000_000);
        assert_eq!(sum, usd_raw(150_250_000_000));
        assert_eq!(sum.to_string(), "150.25 (USD)");
    }

    #[test]
    fn add_negative_element_results_in_zero_element() {
        // -100.05 + 100.05 == 0.
        let net = usd_raw(-100_050_000_000) + usd_raw(100_050_000_000);
        assert_eq!(net, usd_raw(0));
    }

    #[test]
    fn display_crypto() {
        assert_eq!(usdt_raw(12_500_000_000).to_string(), "12.5 (USDT)");
    }

    #[test]
    #[should_panic(expected = "Settlement mismatch: Currency|USD != Currency|EUR")]
    fn add_different_currencies_panics() {
        let _ = usd_raw(1) + eur_raw(1);
    }

    #[test]
    #[should_panic]
    fn add_overflow_panics() {
        // there should be checked_add
        let _ = usd_raw(SettlementNotional::MAX_RAW) + usd_raw(1);
    }

    mod checked_add {
        use super::*;

        #[test]
        fn rejects_currency_mismatch() {
            let err = usd_raw(1).checked_add(eur_raw(1)).unwrap_err();
            assert_eq!(
                err,
                SnAddError::SettlementMismatch(Currency::usd().into(), Currency::eur().into())
            );
            assert_eq!(
                err.to_string(),
                "Settlement mismatch: Currency|USD != Currency|EUR"
            );
        }

        /// USD and USDT are different assets, even though a trader may treat them as one.
        #[test]
        fn rejects_currency_and_crypto_mix() {
            let err = usd_raw(1).checked_add(usdt_raw(1)).unwrap_err();
            assert_eq!(
                err.to_string(),
                "Settlement mismatch: Currency|USD != Crypto|USDT"
            );
        }

        #[test]
        fn mismatch_takes_priority_over_overflow() {
            let err = usd_raw(SettlementNotional::MAX_RAW)
                .checked_add(eur_raw(SettlementNotional::MAX_RAW))
                .unwrap_err();
            assert!(matches!(err, SnAddError::SettlementMismatch(..)));
        }

        #[test]
        fn positive_overflow() {
            let err = usd_raw(SettlementNotional::MAX_RAW)
                .checked_add(usd_raw(1))
                .unwrap_err();
            assert_eq!(err, SnAddError::Overflow(SettlementNotional::MAX_RAW, 1));
            assert!(err.to_string().starts_with("Overflow: "));
        }

        #[test]
        fn negative_overflow() {
            let err = usd_raw(SettlementNotional::MIN_RAW)
                .checked_add(usd_raw(-2))
                .unwrap_err();
            assert_eq!(err, SnAddError::Overflow(SettlementNotional::MIN_RAW, -2));
        }

        /// `i128::MIN` is excluded, so a successful result is always within `MIN_RAW..=MAX_RAW`.
        #[test]
        fn rejects_i128_min() {
            let err = usd_raw(SettlementNotional::MIN_RAW)
                .checked_add(usd_raw(-1))
                .unwrap_err();
            assert_eq!(err, SnAddError::Overflow(SettlementNotional::MIN_RAW, -1));
        }

        /// Malicious `SettlementNotional::new` input will be reported as Overflow.
        ///
        /// A little bit... Desicive. But it makes `new` more ergonomic.
        /// And the only desicive arm is 128::MIN, so... I take it.
        #[test]
        fn out_of_range_operand_is_rejected() {
            let err = SettlementNotional::new(i128::MIN, usd().settlement)
                .checked_add(usd_raw(0))
                .unwrap_err();
            assert_eq!(err, SnAddError::Overflow(i128::MIN, 0));
        }

        /// Regression guards.
        mod preserve_behavior {
            use super::*;
            use proptest::prelude::*;

            #[test]
            fn sums_and_keeps_tag() {
                let sum = usd_raw(100_050_000_000)
                    .checked_add(usd_raw(50_200_000_000))
                    .expect("same currency, no overflow");
                assert_eq!(sum, usd_raw(150_250_000_000));
                assert_eq!(sum.to_string(), "150.25 (USD)");
            }

            #[test]
            fn zero_is_identity() {
                let a = usd_raw(552_812_500_000_000);
                assert_eq!(a.checked_add(usd_raw(0)), Ok(a));
                assert_eq!(usd_raw(0).checked_add(a), Ok(a));
            }

            #[test]
            #[should_panic(expected = "Overflow")]
            fn add_panics_where_checked_add_rejects() {
                let _ = usd_raw(SettlementNotional::MIN_RAW) + usd_raw(-1);
            }

            proptest! {
                /// `Add = checked_add` when succeeds.
                #[test]
                fn agrees_with_add_wherever_checked_add_succeeds(
                    a in any::<i128>(), b in any::<i128>(),
                ) {
                    if let Ok(sum) = usd_raw(a).checked_add(usd_raw(b)) {
                        prop_assert_eq!(usd_raw(a) + usd_raw(b), sum);
                    }
                }
            }
        }
    }
}
