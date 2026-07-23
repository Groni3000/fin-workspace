#[cfg(feature = "serde")]
use std::borrow::Cow;
use std::{
    fmt::Display,
    num::ParseIntError,
    ops::{Mul, Neg},
    str::FromStr,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{price::Price, quantity::Quantity};

/// Has fixed scale and max value.
///
/// Max/min values are derived from max/min `Price` and max `Quantity`.
/// Therefore we can afford to return value, instead of `Option<QuoteNotional>`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct QuoteNotional {
    value: i128,
}

impl QuoteNotional {
    pub const PRECISION: u32 = 9;
    pub const SCALE: i128 = 10_i128.pow(Self::PRECISION);
    // --- max / min shinanigans

    // --- other
    const MAX_PRICE: i128 = Price::MAX_RAW as i128;
    const MAX_QUANTITY: i128 = Quantity::MAX_RAW as i128;
    const MIN_PRICE: i128 = Price::MIN_RAW as i128;

    // --- quote_notional
    pub const MAX_RAW: i128 = Self::round(Self::MAX_QUANTITY * Self::MAX_PRICE);
    pub const MIN_RAW: i128 = Self::round(Self::MAX_QUANTITY * Self::MIN_PRICE);

    // --- Useful constants
    pub const ZERO: Self = Self::new_unchecked(0);
    pub const ONE: Self = Self::new_unchecked(Self::SCALE);
    pub const MAX_INTEGER_PART: i128 = Self::MAX_RAW / Self::SCALE;
    pub const MAX: Self = Self::new_unchecked(Self::MAX_RAW);
    pub const MIN: Self = Self::new_unchecked(Self::MIN_RAW);

    // Powers of ten indexed by remaining precision (0..=PRECISION), so the
    // per-parse scaling is a table lookup instead of a runtime `pow`.
    const POW10: [i128; Self::PRECISION as usize + 1] = [
        1,
        10,
        100,
        1_000,
        10_000,
        100_000,
        1_000_000,
        10_000_000,
        100_000_000,
        1_000_000_000,
    ];

    pub fn new(value: i128) -> Option<Self> {
        if !(Self::MIN_RAW..=Self::MAX_RAW).contains(&value) {
            return None;
        }

        Some(Self { value })
    }

    const fn new_unchecked(value: i128) -> Self {
        Self { value }
    }

    pub fn value(self) -> i128 {
        self.value
    }

    /// Basically this function makes a lot of assumptions about
    /// underlying data correctness.
    ///
    /// No checks at all, pure `happy path`.
    ///
    /// Safe to use when you've already checked and sanitized the input.
    ///
    /// - integer part within ±MAX_INTEGER_PART (else silent overflow in release),
    /// - no `-` anywhere in the fraction (like `0.-4` otherwise - silent wrong value),
    /// - ≤9 fraction digits, non-empty, no whitespace, ≤1 dot (these merely panic).
    pub fn from_str_unchecked(s: &str) -> Self {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, "000000000"));
        let is_negative = integer.starts_with('-');

        let parsed_integer = i128::from_str(integer).unwrap().abs();

        let used_precision = fraction.len();
        let remaining_precision = Self::PRECISION - used_precision as u32;
        let parsed_fraction = i128::from_str(fraction).unwrap();
        let adjusted_fraction = parsed_fraction * Self::POW10[remaining_precision as usize];

        let combined = match is_negative {
            true => -(parsed_integer * Self::SCALE + adjusted_fraction),
            false => parsed_integer * Self::SCALE + adjusted_fraction,
        };

        Self::new_unchecked(combined)
    }

    /// Rounds the value half away from zero.
    ///
    /// In order to understand what I'm trying to achieve -
    /// here is an examples in f64:
    ///
    /// 0.5 -> 1, 0.4 -> 0.0,
    /// -0.5 -> -1, -0.4 -> 0.0
    ///
    /// Assuming `min < value < max` of `QuoteNotional`
    pub const fn round(value: i128) -> i128 {
        // 0.05 == 500_000
        // (500_000 + 1_000_000_000 / 2) / 1_000_000_000
        // (500_000 + 500_000_000) / 1_000_000_000
        // 500_500_000 / 1_000_000_000
        // 0
        //
        // 0.499_999_999 = 499_999_999
        // (499_999_999 + 1_000_000_000 / 2) / 1_000_000_000
        // (499_999_999 + 500_000_000) / 1_000_000_000
        // 999_999_999 / 1_000_000_000
        // 0
        //
        // 500_000_000
        // (500_000_000 + 1_000_000_000 / 2) / 1_000_000_000
        // (500_000_000 + 500_000_000) / 1_000_000_000
        // 1_000_000_000 / 1_000_000_000
        // 1
        (value + value.signum() * (Self::SCALE / 2)) / Self::SCALE
    }
}

impl Neg for QuoteNotional {
    type Output = QuoteNotional;
    fn neg(self) -> Self {
        QuoteNotional::new_unchecked(-self.value())
    }
}

impl Mul<Quantity> for Price {
    type Output = QuoteNotional;

    fn mul(self, rhs: Quantity) -> Self::Output {
        // can't overflow by design
        let mul_res = self.value() as i128 * rhs.value() as i128;
        let raw = QuoteNotional::round(mul_res);
        QuoteNotional::new_unchecked(raw)
    }
}

impl Mul<Price> for Quantity {
    type Output = QuoteNotional;

    fn mul(self, rhs: Price) -> Self::Output {
        rhs * self
    }
}

impl Display for QuoteNotional {
    /// Display is used for serialization. Previous implementation
    /// was working, but could be broken if I decided to bump up
    /// max integer part.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // unsigned_abs can't overflow, even at i128::MIN
        let abs = self.value.unsigned_abs();
        let integer = abs / Self::SCALE as u128;
        let mut fraction = abs % Self::SCALE as u128;

        if self.value < 0 {
            write!(f, "-")?;
        }
        if fraction == 0 {
            return write!(f, "{integer}");
        }
        // Trim trailing zeros, tracking the width the rest must still pad to:
        let mut width = Self::PRECISION as usize;
        while fraction.is_multiple_of(10) {
            fraction /= 10;
            width -= 1;
        }
        write!(f, "{integer}.{fraction:0width$}")
    }
}

impl From<QuoteNotional> for f64 {
    fn from(value: QuoteNotional) -> Self {
        value.value as f64 / QuoteNotional::SCALE as f64
    }
}

impl From<QuoteNotional> for i128 {
    fn from(value: QuoteNotional) -> Self {
        value.value
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseQuoteNotionalError {
    InvalidFormat,
    OutOfBounds,
    PrecisionError(usize),
    ParseIntError(ParseIntError),
}

impl Display for ParseQuoteNotionalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseQuoteNotionalError::InvalidFormat => write!(f, "Invalid format"),
            ParseQuoteNotionalError::OutOfBounds => write!(f, "Out of bounds"),
            ParseQuoteNotionalError::PrecisionError(precision) => {
                write!(f, "Precision error: {}", precision)
            }
            ParseQuoteNotionalError::ParseIntError(err) => err.fmt(f),
        }
    }
}

impl FromStr for QuoteNotional {
    type Err = ParseQuoteNotionalError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, "000000000"));
        let (integer, fraction) = (integer.trim(), fraction.trim());
        // Check below needed to not accept and parse `-0.-1`
        // The fraction part would be parsed no problem
        if fraction.starts_with('-') {
            return Err(ParseQuoteNotionalError::InvalidFormat);
        }
        let is_negative = integer.starts_with('-');

        let parsed_integer =
            i128::from_str(integer).map_err(ParseQuoteNotionalError::ParseIntError)?;
        if !(-Self::MAX_INTEGER_PART..=Self::MAX_INTEGER_PART).contains(&parsed_integer) {
            return Err(ParseQuoteNotionalError::OutOfBounds);
        }
        // We do it after min/max check because i128::MIN.abs() would panic
        let parsed_integer = parsed_integer.abs();

        let used_precision = fraction.len();
        if used_precision > Self::PRECISION as usize {
            return Err(ParseQuoteNotionalError::PrecisionError(used_precision));
        }
        let remaining_precision = Self::PRECISION - used_precision as u32;
        let parsed_fraction =
            i128::from_str(fraction).map_err(ParseQuoteNotionalError::ParseIntError)?;
        let adjusted_fraction = parsed_fraction * Self::POW10[remaining_precision as usize];

        let combined = match is_negative {
            true => -(parsed_integer * Self::SCALE + adjusted_fraction),
            false => parsed_integer * Self::SCALE + adjusted_fraction,
        };
        if !(-Self::MAX_RAW..=Self::MAX_RAW).contains(&combined) {
            return Err(ParseQuoteNotionalError::OutOfBounds);
        }

        Ok(Self::new_unchecked(combined))
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for QuoteNotional {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s: Cow<'de, str> = Deserialize::deserialize(deserializer)?;
        Self::from_str(&s).map_err(serde::de::Error::custom)
    }
}

#[cfg(feature = "serde")]
impl Serialize for QuoteNotional {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.collect_str(self)
    }
}

#[cfg(test)]
mod tests {
    // Bring the macros and other important things into scope.
    use proptest::prelude::*;
    use std::assert_matches;

    use super::*;

    #[test]
    fn test_quote_notional_new() {
        let max = QuoteNotional::new(QuoteNotional::MAX_RAW).unwrap();
        assert_eq!(QuoteNotional::MAX_RAW, max.value);

        let min = QuoteNotional::new(QuoteNotional::MIN_RAW).unwrap();
        assert_eq!(QuoteNotional::MIN_RAW, min.value);

        assert!(QuoteNotional::new(QuoteNotional::MAX_RAW + 1).is_none());
        assert!(QuoteNotional::new(QuoteNotional::MIN_RAW - 1).is_none());
    }

    #[test]
    fn neg_is_symmetric_at_bounds() {
        // Bounds are symmetric (MIN_RAW == -MAX_RAW)
        assert_eq!(-QuoteNotional::MAX, QuoteNotional::MIN);
        assert_eq!(-QuoteNotional::MIN, QuoteNotional::MAX);
        assert_eq!(-QuoteNotional::ZERO, QuoteNotional::ZERO);
    }

    proptest! {
        #[test]
        fn neg_negates_value_and_is_involution(
            raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW,
        ) {
            let x = QuoteNotional::new_unchecked(raw);
            // Single negation flips the raw value
            prop_assert_eq!((-x).value(), -raw);
            // And negating twice is the identity.
            prop_assert_eq!(-(-x), x);
        }
    }

    #[test]
    fn test_str_to_quote_notional_conversions() {
        let input = "";
        let qn = QuoteNotional::from_str(input);
        assert_matches!(qn, Err(ParseQuoteNotionalError::ParseIntError(_)));

        let input = "1";
        let qn = QuoteNotional::from_str(input);
        assert!(qn.is_ok_and(|x| x.eq(&QuoteNotional::new_unchecked(1_000_000_000))));

        let input = "1.0";
        let qn = QuoteNotional::from_str(input);
        assert!(qn.is_ok_and(|x| x.eq(&QuoteNotional::new_unchecked(1_000_000_000))));

        let input = "-1.0";
        let qn = QuoteNotional::from_str(input);
        assert!(qn.is_ok_and(|x| x.eq(&QuoteNotional::new_unchecked(-1_000_000_000))));

        let input = "-0.5";
        let qn = QuoteNotional::from_str(input);
        assert!(qn.is_ok_and(|x| x.eq(&QuoteNotional::new_unchecked(-500_000_000))));

        let input = "1.5";
        let qn = QuoteNotional::from_str(input);
        assert!(qn.is_ok_and(|x| x.eq(&QuoteNotional::new_unchecked(1_500_000_000))));

        let input = "1.-5";
        let qn = QuoteNotional::from_str(input);
        assert_matches!(qn, Err(ParseQuoteNotionalError::InvalidFormat));
    }

    proptest! {
        #[test]
        fn is_some_for_small_integers(s in (-10_i128..10_i128)) {
            assert!(QuoteNotional::new(s).is_some());
        }

        #[test]
        fn is_some_for_large_positive_integers(s in (QuoteNotional::MAX_RAW - 10)..=QuoteNotional::MAX_RAW) {
            assert!(QuoteNotional::new(s).is_some());
        }

        #[test]
        fn is_none_for_large_positive_integers(s in (QuoteNotional::MAX_RAW + 1)..=(QuoteNotional::MAX_RAW + 11)) {
            assert!(QuoteNotional::new(s).is_none());
        }

        #[test]
        fn is_some_for_large_negative_integers(s in QuoteNotional::MIN_RAW..=(QuoteNotional::MIN_RAW + 10)) {
            assert!(QuoteNotional::new(s).is_some());
        }

        #[test]
        fn is_none_for_large_negative_integers(s in (QuoteNotional::MIN_RAW - 11)..=(QuoteNotional::MIN_RAW - 1)) {
            assert!(QuoteNotional::new(s).is_none());
        }
    }

    proptest! {
        #[test]
        fn str_for_in_range_raw(raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW) {
            let s = canonical_display(raw);
            let got = QuoteNotional::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == raw),
                "s={s} raw={raw} got={got:?}"
            );
        }

        // Correct scaling: 0.5 -> 500_000_000_000_000_000
        #[test]
        fn str_scales_fraction_by_position(
            neg in any::<bool>(),
            int in 0_i128..QuoteNotional::MAX_INTEGER_PART,
            len in 1_usize..=QuoteNotional::PRECISION as usize,
            seed in 0_u64..QuoteNotional::SCALE as u64,
        ) {
            let frac = seed % 10_u64.pow(len as u32); // fits in `len` digits
            let sign = if neg { "-" } else { "" };
            let s = format!("{sign}{int}.{frac:0len$}"); // zero-pad to `len`
            let magnitude =
                int * QuoteNotional::SCALE + frac as i128 * 10_i128.pow(QuoteNotional::PRECISION - len as u32);
            let expected = if neg { -magnitude } else { magnitude };
            let got = QuoteNotional::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == expected),
                "s={s} expected={expected} got={got:?}"
            );
        }

        // Precision: more than 9 fractional digits must be rejected.
        #[test]
        fn str_rejects_excess_precision(
            int in 0_i128..QuoteNotional::MAX_INTEGER_PART,
            len in (QuoteNotional::PRECISION as usize + 1)..=20_usize,
            seed in any::<u64>(),
        ) {
            let frac: String = (0..len)
                .map(|i| char::from(b'0' + ((seed >> (i % 60)) % 10) as u8))
                .collect();
            let s = format!("{int}.{frac}");
            let got = QuoteNotional::from_str(&s);
            prop_assert!(
                matches!(got, Err(ParseQuoteNotionalError::PrecisionError(_))),
                "s={s} got={got:?}"
            );
        }

        // Bounds: an integer part beyond ±MAX_INTEGER_PART must be OutOfBounds
        #[test]
        fn str_rejects_large_integer_part(
            int in (QuoteNotional::MAX_INTEGER_PART + 1)..=(QuoteNotional::MAX_INTEGER_PART + 1_000_i128),
            neg in any::<bool>(),
        ) {
            let s = format!("{}{int}.0", if neg { "-" } else { "" });
            let got = QuoteNotional::from_str(&s);
            prop_assert!(
                matches!(got, Err(ParseQuoteNotionalError::OutOfBounds)),
                "s={s} got={got:?}"
            );
        }

        // Boundary: only fractions up to `MAX_RAW % SCALE` stay in range.
        #[test]
        fn str_accepts_max_integer_with_fraction(
            neg in any::<bool>(),
            frac_units in 0_i128..=(QuoteNotional::MAX_RAW % QuoteNotional::SCALE),
        ) {
            let sign = if neg { "-" } else { "" };
            let s = format!("{sign}{}.{frac_units:09}", QuoteNotional::MAX_INTEGER_PART);
            let magnitude = QuoteNotional::MAX_INTEGER_PART * QuoteNotional::SCALE + frac_units;
            let expected = if neg { -magnitude } else { magnitude };
            let got = QuoteNotional::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == expected),
                "s={s} expected={expected} got={got:?}"
            );
        }

        // Out of Boundary: the same test but for rejects `MAX_RAW % SCALE + 1`.
        #[test]
        fn str_rejects_max_integer_overshoot_fraction(
            neg in any::<bool>(),
            frac_units in (QuoteNotional::MAX_RAW % QuoteNotional::SCALE + 1)..QuoteNotional::SCALE,
        ) {
            let sign = if neg { "-" } else { "" };
            let s = format!("{sign}{}.{frac_units:09}", QuoteNotional::MAX_INTEGER_PART);
            let got = QuoteNotional::from_str(&s);
            prop_assert!(
                matches!(got, Err(ParseQuoteNotionalError::OutOfBounds)),
                "s={s} got={got:?}"
            );
        }

    }

    #[test]
    fn display_formats_known_values() {
        // Base cases
        let cases = [
            (0_i128, "0"),
            (1, "0.000000001"),
            (-1, "-0.000000001"),
            (100_000_000, "0.1"),
            (2_000_000_000, "2"),
            (-5_300_000_000, "-5.3"),
            (QuoteNotional::SCALE, "1"),
            (2 * QuoteNotional::SCALE, "2"),
            (-5_300_000_000, "-5.3"),
            (QuoteNotional::MAX_RAW, "5000006000000.993999998"),
            (QuoteNotional::MIN_RAW, "-5000006000000.993999998"),
        ];
        for (raw, expected) in cases {
            let p = QuoteNotional::new(raw).unwrap();
            assert_eq!(p.to_string(), expected, "raw={raw}");
        }
    }

    #[test]
    fn display_integer_path_drops_dot() {
        for int in [0_i128, 1, 42, QuoteNotional::MAX_INTEGER_PART] {
            let raw = int * QuoteNotional::SCALE;
            assert_eq!(
                QuoteNotional::new(raw).unwrap().to_string(),
                int.to_string()
            );
            if int != 0 {
                let n = QuoteNotional::new(-raw).unwrap();
                assert_eq!(n.to_string(), format!("-{int}"));
            }
        }
    }

    proptest! {
        // `from_str_unchecked` must agree with the checked parser correct input.
        #[test]
        fn from_str_unchecked_matches_checked(raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW) {
            let s = canonical_display(raw);
            prop_assert_eq!(
                QuoteNotional::from_str_unchecked(&s).value(),
                QuoteNotional::from_str(&s).unwrap().value(),
                "s={}", s
            );
        }

        // Bare integers (no dot) appending `.(0)`
        #[test]
        fn from_str_unchecked_bare_integer(int in -QuoteNotional::MAX_INTEGER_PART..=QuoteNotional::MAX_INTEGER_PART) {
            let s = int.to_string();
            prop_assert_eq!(
                QuoteNotional::from_str_unchecked(&s).value(),
                int * QuoteNotional::SCALE,
                "s={}", s
            );
        }
    }

    // --------------------------------------
    // ---        Utility function        ---
    // --- Canonical QuoteNotional representation ---
    // --------------------------------------
    fn canonical_display(raw: i128) -> String {
        let sign = if raw < 0 { "-" } else { "" };
        let a = raw.unsigned_abs();
        let int = a / QuoteNotional::SCALE as u128;
        let frac = a % QuoteNotional::SCALE as u128;
        if frac == 0 {
            format!("{sign}{int}")
        } else {
            format!("{sign}{int}.{}", format!("{frac:09}").trim_end_matches('0'))
        }
    }

    proptest! {
        // --------------------------
        // --- Serialize and back ---
        // --------------------------
        #[test]
        fn display_roundtrips_through_from_str(raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW) {
            let p = QuoteNotional::new(raw).unwrap();
            let s = p.to_string();
            let got = QuoteNotional::from_str(&s);
            prop_assert!(
                matches!(got, Ok(q) if q.value() == raw),
                "raw={raw} s={s} got={got:?}"
            );
        }

        // ---------------------------------
        // --- .to_string() is Canonical ---
        // ---------------------------------
        #[test]
        fn display_matches_canonical(raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW) {
            let p = QuoteNotional::new(raw).unwrap();
            prop_assert_eq!(p.to_string(), canonical_display(raw), "raw={}", raw);
        }
    }

    // -----------------------
    // ---      round      ---
    // -----------------------
    /// This is the reference implementation of `round` for tests.
    fn round_ref(v: i128) -> i128 {
        let q = v / QuoteNotional::SCALE; // truncates toward zero
        let r = (v % QuoteNotional::SCALE).abs();
        if r * 2 >= QuoteNotional::SCALE {
            q + v.signum()
        } else {
            q
        }
    }

    #[test]
    fn round_known_values() {
        let s = QuoteNotional::SCALE;
        let cases = [
            (0, 0),
            (-0, 0),           // -0 -> 0 (sign gone away)
            (s / 2, 1),        // 0.5 -> 1  (tie, away)
            (s / 2 - 1, 0),    // just under 0.5 -> 0
            (s / 2 + 1, 1),    // just over  0.5 -> 1
            (-(s / 2), -1),    // -0.5 -> -1 (tie, away)
            (-(s / 2 - 1), 0), // -0.4… -> 0
            (s + s / 2, 2),    // 1.5 -> 2
            (2 * s, 2),        // exact, no fraction
        ];
        for (v, expected) in cases {
            assert_eq!(QuoteNotional::round(v), expected, "v={v}");
        }
    }

    #[test]
    fn round_is_linear_transformation() {
        // round(-v) == -round(v)
        for v in [1_i128, 499_999_999, 500_000_000, 500_000_001, 1_500_000_000] {
            assert_eq!(QuoteNotional::round(-v), -QuoteNotional::round(v), "v={v}");
        }
    }

    proptest! {
        // Check that `round` matches the reference implementation.
        #[test]
        fn round_matches_reference(v in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW) {
            prop_assert_eq!(QuoteNotional::round(v), round_ref(v), "v={}", v);
        }
    }

    // ---------------------------------
    // ---   Price * Quantity mul   ---
    // ---------------------------------
    #[test]
    fn mul_produces_expected_value_and_display() {
        let price = Price::new(2_150_000_000).unwrap();
        let qty = Quantity::new(3_000_000_000).unwrap();
        let qn = price * qty;
        assert_eq!(qn.value(), 6_450_000_000);
        assert_eq!(qn.to_string(), "6.45");
    }

    #[test]
    fn mul_rounds_half_away() {
        // result is in 10th digit, applied round
        // 0.000000005 * 0.1 = 0.0000000005
        // rounds away from zero to 0.000000001.
        let tiny = Price::new(5).unwrap();
        let tenth = Quantity::new(100_000_000).unwrap();
        assert_eq!((tiny * tenth).value(), 1);

        // Negative side of the same tie.
        let neg_tiny = Price::new(-5).unwrap();
        assert_eq!((neg_tiny * tenth).value(), -1);

        // Below the tie stays down:
        // 1.000000001 * 1.000000001 =
        // 1.000000002000000001 =
        //                    | this last digit will be rounded to 0
        // 1.000000002 - result
        let a = Price::new(1_000_000_001).unwrap();
        let b = Quantity::new(1_000_000_001).unwrap();
        assert_eq!((a * b).value(), 1_000_000_002);
    }

    #[test]
    fn mul_hits_bounds_exactly() {
        // The extremes of Price/Quantity land exactly on QuoteNotional's bounds
        let max_price = Price::new(Price::MAX_RAW).unwrap();
        let min_price = Price::new(Price::MIN_RAW).unwrap();
        let max_qty = Quantity::new(Quantity::MAX_RAW).unwrap();

        assert_eq!((max_price * max_qty).value(), QuoteNotional::MAX_RAW);
        assert_eq!((min_price * max_qty).value(), QuoteNotional::MIN_RAW);
    }

    proptest! {
        // "Can't overflow by design": any valid Price * Quantity lands inside
        // [MIN_RAW, MAX_RAW], so new() would accept every product.
        #[test]
        fn mul_stays_in_range(
            p_raw in Price::MIN_RAW..=Price::MAX_RAW,
            q_raw in Quantity::MIN_RAW..=Quantity::MAX_RAW,
        ) {
            // It uses `new_unchecked` under the hood, but if it happens
            // I change it - I may catch the bug here.
            let qn = Price::new(p_raw).unwrap() * Quantity::new(q_raw).unwrap();
            prop_assert!(
                QuoteNotional::new(qn.value()).is_some(),
                "p_raw={p_raw} q_raw={q_raw} qn={}", qn.value()
            );
        }

        // Multiplication is commutative.
        #[test]
        fn mul_is_commutative(
            p_raw in Price::MIN_RAW..=Price::MAX_RAW,
            q_raw in Quantity::MIN_RAW..=Quantity::MAX_RAW,
        ) {
            let price = Price::new(p_raw).unwrap();
            let qty = Quantity::new(q_raw).unwrap();
            prop_assert_eq!((price * qty).value(), (qty * price).value());
        }

        // `mul` rounds so `round(mul_result)` is no-op
        #[test]
        fn mul_matches_rounded_raw_product(
            p_raw in Price::MIN_RAW..=Price::MAX_RAW,
            q_raw in Quantity::MIN_RAW..=Quantity::MAX_RAW,
        ) {
            let qn = Price::new(p_raw).unwrap() * Quantity::new(q_raw).unwrap();
            let expected = QuoteNotional::round(p_raw as i128 * q_raw as i128);
            prop_assert_eq!(qn.value(), expected, "p_raw={} q_raw={}", p_raw, q_raw);
        }
    }
}
