use std::{fmt::Display, num::ParseIntError, ops::Add};

use crate::{currency::CurrencyTag, price::Price};

/// Has fixed scale and max value.
///
/// Pretty similar to `QuoteNotional`.
///
/// `CurrencyNotional` is usually a result of multiplication of `QuoteNotional` by `PointValue`.
///
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CurrencyNotional {
    // value: i128 = 16 bytes. Align = 16 bytes.
    // If I use `Currency` with size 24 bytes
    // => `CurrencyNotional` = 16 + 24 + 8 (padding) = 48 bytes
    // I can make it smaller by removing `Currency.name` (16 bytes)
    // and numeric code (3 bytes).
    //
    // Then size of `Currency` will be 3 + 1 = 4 (bytes)
    // => size of CurrencyNotional = 16 + 4 + 12 (padding) = 32 bytes.
    value: i128,
    currency: CurrencyTag,
}

impl CurrencyNotional {
    pub const SCALE: i128 = Price::SCALE as i128;
    pub const PRECISION: i128 = 9;

    pub const ONE_RAW: i128 = Self::SCALE;
    pub const ZERO_RAW: i128 = 0_i128;
    pub const MAX_RAW: i128 = i128::MAX;
    /// Though it is declared, I do not use it.
    ///
    /// It would be naturally used in `Self::new`
    /// and ignored in `Self::new_unchecked`, but...
    ///
    /// It seems to be a very rare problem.
    ///
    /// Regardless, what can happen?
    /// Debug: panic
    /// Release: negate i128::MIN will be identity mapping
    /// CurrencyNotional(i128::MIN).neg() == CurrencyNotional(i128::MIN)
    ///
    /// I don't know... We can get it only from raw
    /// `CurrencyNotional::new(i128::MIN...)` it's just... Malicious?
    /// Do I really want to protect from such code?
    pub const MIN_RAW: i128 = -Self::MAX_RAW;
    pub const MAX_INTEGER_PART: i128 = Self::MAX_RAW / Self::SCALE;

    /// Construct a `CurrencyNotional` from a raw value and currency tag.
    ///
    /// # Note
    ///
    /// `value == i128::MIN` can lead to problems described in `CurrencyNotional::MIN_RAW`.
    pub const fn new(value: i128, currency: CurrencyTag) -> Self {
        Self { value, currency }
    }

    pub fn value(&self) -> i128 {
        self.value
    }
}

impl Add for CurrencyNotional {
    type Output = CurrencyNotional;

    /// Perform checked add, panic on overflow or different currencies.
    fn add(self, rhs: Self) -> Self::Output {
        if self.currency != rhs.currency {
            panic!("Cannot add different currencies");
        }
        CurrencyNotional::new(self.value.checked_add(rhs.value).unwrap(), self.currency)
    }
}

impl Display for CurrencyNotional {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.value.is_negative() {
            write!(f, "-")?;
        }

        let abs = self.value.unsigned_abs();
        let integer_part = abs / Self::SCALE as u128;
        let mut fractional_part = abs % Self::SCALE as u128;
        if fractional_part == 0 {
            return write!(f, "{} ({})", integer_part, self.currency);
        }

        let mut pow = Self::PRECISION as usize;
        while fractional_part.is_multiple_of(10) {
            fractional_part /= 10;
            pow -= 1;
        }
        write!(
            f,
            "{}.{:0pow$} ({})",
            integer_part, fractional_part, self.currency
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseCurrencyNotionalError {
    InvalidFormat,
    OutOfBounds,
    PrecisionError(usize),
    ParseIntError(ParseIntError),
}

impl Display for ParseCurrencyNotionalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseCurrencyNotionalError::InvalidFormat => write!(f, "Invalid format"),
            ParseCurrencyNotionalError::OutOfBounds => write!(f, "Out of bounds"),
            ParseCurrencyNotionalError::PrecisionError(precision) => {
                write!(f, "Precision error: {}", precision)
            }
            ParseCurrencyNotionalError::ParseIntError(err) => err.fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::currency::Currency;

    // helper
    fn usd() -> CurrencyNotional {
        CurrencyNotional::new(0, Currency::usd().into())
    }

    // helper that uses helper
    fn usd_raw(raw: i128) -> CurrencyNotional {
        CurrencyNotional::new(raw, usd().currency)
    }

    fn eur_raw(raw: i128) -> CurrencyNotional {
        CurrencyNotional::new(raw, Currency::eur().into())
    }

    #[test]
    fn display_half_dollar_fraction() {
        assert_eq!(usd_raw(552_812_500_000_000).to_string(), "552812.5 (USD)");
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
        assert_eq!(usd_raw(552_812_000_000_000).to_string(), "552812 (USD)");
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
    #[should_panic(expected = "Cannot add different currencies")]
    fn add_different_currencies_panics() {
        let _ = usd_raw(1) + eur_raw(1);
    }

    #[test]
    #[should_panic]
    fn add_overflow_panics() {
        // there should be checked_add
        let _ = usd_raw(CurrencyNotional::MAX_RAW) + usd_raw(1);
    }
}
