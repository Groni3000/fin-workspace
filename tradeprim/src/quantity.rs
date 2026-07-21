#[cfg(feature = "serde")]
use std::borrow::Cow;
use std::{fmt::Display, num::ParseIntError, str::FromStr};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Has fixed scale and max value.
///
/// Non-zero number that follows such rules:
/// ( ✗ means `not implemented`)
/// ✗ Quantity - Quantity -> QuantityDelta<i64>
/// ✗ Price * Quantity<u64> -> Notional<i128?>
/// ✗ Notional<i128> / Quantity<u64> -> Price<i64>
/// ✗ Quantity<u64> + Quantity<u64> -> Quantity<u64>
///
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Quantity {
    value: u64,
}

impl Quantity {
    // u64::MAX
    // 18_446_744_073_709_551_615
    //                999_999_999
    //      9_999_999_
    // So, we have 4 digits to spare
    // What's realistic quantity?
    //
    // Databento uses u32 for quantity in `trades` dataschema.
    // u32::MAX
    // 4_294_967_295
    // So, I assume, 5e6 max integer part is ok
    pub const PRECISION: u32 = 9;
    /// 1e9
    pub const SCALE: u64 = 10_u64.pow(Self::PRECISION);
    /// 5e6
    pub const MAX_INTEGER_PART: u64 = 5_000_000;
    /// 5_000_000.999_999_999 (max integer part with a full fraction)
    pub const MAX_RAW: u64 = Self::MAX_INTEGER_PART * Self::SCALE + (Self::SCALE - 1);
    /// 0_000_000.000_000_000
    pub const MIN_RAW: u64 = 0;
    /// Zero value
    pub const ZERO: Self = Self::new_unchecked(0);
    // Powers of ten indexed by remaining precision (0..=PRECISION), so the
    // per-parse scaling is a table lookup instead of a runtime `pow`.
    const POW10: [u64; Self::PRECISION as usize + 1] = [
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

    pub fn new(value: u64) -> Option<Self> {
        if value > Self::MAX_RAW {
            return None;
        }

        Some(Self { value })
    }

    const fn new_unchecked(value: u64) -> Self {
        Self { value }
    }

    pub fn value(self) -> u64 {
        self.value
    }

    /// Basically this function makes a lot of assumptions about
    /// underlying data correctness.
    ///
    /// No checks at all, pure `happy path`.
    ///
    /// Safe to use when you've already checked and sanitized the input.
    ///
    /// - integer part is in [MIN, MAX_INTEGER_PART] (else silent overflow in release),
    /// - no `-` anywhere (like `-0.-4` otherwise - panic),
    /// - ≤9 fraction digits, non-empty, no whitespace, ≤1 dot (these merely panic).
    pub fn from_str_unchecked(s: &str) -> Self {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, "000000000"));

        let parsed_uint = u64::from_str(integer).unwrap();

        let used_precision = fraction.len();
        let remaining_precision = Self::PRECISION - used_precision as u32;
        let parsed_fraction = u64::from_str(fraction).unwrap();
        let adjusted_fraction = parsed_fraction * Self::POW10[remaining_precision as usize];

        let combined = parsed_uint * Self::SCALE + adjusted_fraction;

        Self::new_unchecked(combined)
    }
}

impl Display for Quantity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let int = self.value / Self::SCALE;
        let frac = self.value % Self::SCALE;
        if frac == 0 {
            write!(f, "{int}")
        } else {
            write!(f, "{int}.{}", format!("{frac:09}").trim_end_matches('0'))
        }
    }
}

impl From<Quantity> for f64 {
    fn from(value: Quantity) -> Self {
        value.value as f64 / Quantity::SCALE as f64
    }
}

impl From<Quantity> for u64 {
    fn from(value: Quantity) -> Self {
        value.value
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseQuantityError {
    InvalidFormat,
    OutOfBounds,
    PrecisionError(usize),
    ParseIntError(ParseIntError),
}

impl From<ParseIntError> for ParseQuantityError {
    fn from(value: ParseIntError) -> Self {
        ParseQuantityError::ParseIntError(value)
    }
}

impl Display for ParseQuantityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseQuantityError::InvalidFormat => write!(f, "Invalid format"),
            ParseQuantityError::OutOfBounds => write!(f, "Out of bounds"),
            ParseQuantityError::PrecisionError(precision) => {
                write!(f, "Precision error: {}", precision)
            }
            ParseQuantityError::ParseIntError(err) => err.fmt(f),
        }
    }
}

impl FromStr for Quantity {
    type Err = ParseQuantityError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, "000000000"));
        let (integer, fraction) = (integer.trim(), fraction.trim());

        let parsed_integer = u64::from_str(integer)?;
        if parsed_integer > Self::MAX_INTEGER_PART {
            return Err(ParseQuantityError::OutOfBounds);
        }

        let used_precision = fraction.len();
        if used_precision > Self::PRECISION as usize {
            return Err(ParseQuantityError::PrecisionError(used_precision));
        }
        let remaining_precision = Self::PRECISION - used_precision as u32;
        let parsed_fraction = u64::from_str(fraction)?;
        let adjusted_fraction = parsed_fraction * Self::POW10[remaining_precision as usize];

        let combined = parsed_integer * Self::SCALE + adjusted_fraction;

        Ok(Self::new_unchecked(combined))
    }
}

/// Errors that can occur when converting a `f64` to a `Quantity`.
/// f64 field is the original value that caused the fail
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FromF64Error {
    OutOfBounds(f64),
    Negative,
}

impl Display for FromF64Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FromF64Error::OutOfBounds(value) => write!(f, "out of bounds: {}", value),
            FromF64Error::Negative => write!(f, "negative value"),
        }
    }
}

impl TryFrom<f64> for Quantity {
    type Error = FromF64Error;

    /// It is approximate near extremes.
    ///
    /// For example:
    /// ```
    /// use tradeprim::quantity::Quantity;
    ///
    /// let value: f64 = 4201101.596639222;
    /// let qty: Quantity = value.try_into().unwrap();
    /// let wrong_value: u64 = 4201101596639223;
    /// assert_eq!(qty.value(), wrong_value);
    /// ```
    fn try_from(value: f64) -> Result<Self, Self::Error> {
        if !value.is_finite() {
            return Err(FromF64Error::OutOfBounds(value));
        }
        if value < 0.0 {
            return Err(FromF64Error::Negative);
        }

        let raw = (value * Self::SCALE as f64).round();
        Self::new(raw as u64).ok_or(FromF64Error::OutOfBounds(value))
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Quantity {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s: Cow<'de, str> = Deserialize::deserialize(deserializer)?;
        Self::from_str(&s).map_err(serde::de::Error::custom)
    }
}

#[cfg(feature = "serde")]
impl Serialize for Quantity {
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
    use std::cmp::Ordering;

    use super::*;

    #[test]
    fn test_quantity_new() {
        let max_quantity = Quantity::new(Quantity::MAX_RAW).unwrap();
        assert_eq!(Quantity::MAX_RAW, max_quantity.value);

        let min_quantity = Quantity::new(Quantity::MIN_RAW).unwrap();
        assert_eq!(Quantity::MIN_RAW, min_quantity.value);

        assert!(Quantity::new(Quantity::MAX_RAW + 1).is_none());
    }

    #[test]
    fn test_f64_to_quantity_conversions() {
        let raw = 65537.273030587;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x.value == 65537_273_030_587));

        // --- Normal cases
        let raw = 100.0;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x.value == 100_000_000_000));

        let raw = 0.000000015;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x.value == 000_000_015));

        let raw = 100.239;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x.value == 100_239_000_000));

        // --- Edge cases (MAX/MIN/ZERO/signed smallest non-zero)
        // --- Near max doesn't work!
        let raw = Quantity::MAX_RAW as f64;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(quantity, Err(FromF64Error::OutOfBounds(_)));

        let raw = Quantity::ZERO.value() as f64;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x == Quantity::ZERO));

        let raw = 0.000000001;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x.value == 1));

        // --- Error cases (too large/precision loss)
        let raw = 0.0000000001; // 1 digit out of precision
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x == Quantity::ZERO));

        let raw = 0.000000000001; // 0.001 - 3 digits out of precision
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x == Quantity::ZERO));

        let raw = 0.0000000000001; // 0.0001 - Should not cause an error
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x == Quantity::ZERO));

        let raw = 0.000_000_000_000_9; // 0.0009 - Should not cause an error
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x == Quantity::ZERO));

        let raw = (Quantity::MAX_INTEGER_PART + 1) as f64; // out of bound by 1 unit
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(quantity, Err(FromF64Error::OutOfBounds(_)));

        let raw = 1_000_000.000000001;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert!(quantity.is_ok_and(|x| x.value == 1_000_000_000_000_001));

        // NAN/INF/NEG_INF
        let raw = f64::NAN;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(quantity, Err(FromF64Error::OutOfBounds(_)));

        let raw = f64::INFINITY;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(quantity, Err(FromF64Error::OutOfBounds(_)));

        let raw = f64::NEG_INFINITY;
        let quantity: Result<Quantity, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(quantity, Err(FromF64Error::OutOfBounds(_)));
    }

    #[test]
    fn test_quantity_to_f64_conversions() {
        let quantity = Quantity::new(0_999_999_999_999_999);
        assert!(quantity.is_some_and(|x| {
            let raw_quantity: f64 = x.into();
            let expected_quantity = 999_999.999_999_999_f64;
            raw_quantity.total_cmp(&expected_quantity) == Ordering::Equal
        }));

        let quantity = Quantity::new(0_999_999_000_000_099);
        assert!(quantity.is_some_and(|x| {
            let raw_quantity: f64 = x.into();
            let expected_quantity = 999_999.000_000_099_f64;
            raw_quantity.total_cmp(&expected_quantity) == Ordering::Equal
        }));

        let quantity = Quantity::new(0_000_000_000_000_099);
        assert!(quantity.is_some_and(|x| {
            let raw_quantity: f64 = x.into();
            let expected_quantity = 0.000_000_099_f64;
            raw_quantity.total_cmp(&expected_quantity) == Ordering::Equal
        }));
    }

    #[test]
    fn test_str_to_quantity_conversions() {
        let input = "";
        let quantity = Quantity::from_str(input);
        assert_matches!(quantity, Err(ParseQuantityError::ParseIntError(_)));

        let input = "1";
        let quantity = Quantity::from_str(input);
        assert!(quantity.is_ok_and(|x| x.eq(&Quantity::new_unchecked(1_000_000_000))));

        let input = "1.0";
        let quantity = Quantity::from_str(input);
        assert!(quantity.is_ok_and(|x| x.eq(&Quantity::new_unchecked(1_000_000_000))));

        let input = "-1.0";
        let quantity = Quantity::from_str(input);
        assert_matches!(quantity, Err(ParseQuantityError::ParseIntError(_)));

        let input = "-0.5";
        let quantity = Quantity::from_str(input);
        assert_matches!(quantity, Err(ParseQuantityError::ParseIntError(_)));

        let input = "1.5";
        let quantity = Quantity::from_str(input);
        assert!(quantity.is_ok_and(|x| x.eq(&Quantity::new_unchecked(1_500_000_000))));

        let input = "1.-5";
        let quantity = Quantity::from_str(input);
        assert_matches!(quantity, Err(ParseQuantityError::ParseIntError(_)));
    }

    proptest! {
        #[test]
        fn is_some_for_small_integers(s in (0_u64..10_u64)) {
            assert!(Quantity::new(s).is_some());
        }

        #[test]
        fn is_some_for_large_positive_integers(s in (Quantity::MAX_RAW - 10)..=Quantity::MAX_RAW) {
            assert!(Quantity::new(s).is_some());
        }

        #[test]
        fn is_none_for_large_positive_integers(s in (Quantity::MAX_RAW + 1)..=(Quantity::MAX_RAW + 11)) {
            assert!(Quantity::new(s).is_none());
        }
    }

    proptest! {
        /// Normal case: every in-range raw value, turned into an f64 quantity and
        /// parsed back, must recover the exact same raw.
        /// (NAN/INF are covered by the unit test above.)
        ///
        /// Extreme case: off by 1 error.
        ///
        /// This test loosens the requirements about upper bound.
        #[test]
        fn f64_roundtrips_for_in_range_raw(raw in Quantity::MIN_RAW..=Quantity::MAX_RAW / 2) {
            let v = raw as f64 / Quantity::SCALE as f64;
            let got = Quantity::try_from(v);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == raw),
                "v={v} raw={raw} got={got:?}"
            );
        }

        // OutOfBounds: whole-number magnitudes just past ±1e6. Kept small enough
        // that `major * SCALE` is an exact f64 integer, so the only reason to
        // reject is the bounds check (not precision).
        #[test]
        fn out_of_bounds_for_large_magnitude(major in Quantity::MAX_INTEGER_PART+1..=Quantity::MAX_INTEGER_PART + 1000_u64) {
                let got = Quantity::try_from(major as f64);
                prop_assert!(matches!(got, Err(FromF64Error::OutOfBounds(_))),"major={major} got={got:?}");
        }
    }

    // Canonical decimal string for a raw value: always 9 fractional digits.
    fn canonical_display(raw: u64) -> String {
        let int = raw / Quantity::SCALE as u64;
        let frac = raw % Quantity::SCALE as u64;
        format!("{int}.{frac:09}")
    }

    proptest! {
        #[test]
        fn str_for_in_range_raw(raw in Quantity::MIN_RAW..=Quantity::MAX_RAW) {
            let s = canonical_display(raw);
            let got = Quantity::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == raw),
                "s={s} raw={raw} got={got:?}"
            );
        }

        // Correct scaling: 0.5 -> 500_000_000
        #[test]
        fn str_scales_fraction_by_position(
            int in 0_u64..Quantity::MAX_INTEGER_PART,
            len in 1_usize..=Quantity::PRECISION as usize,
            seed in 0_u64..Quantity::SCALE as u64,
        ) {
            let frac = seed % 10_u64.pow(len as u32); // fits in `len` digits
            let s = format!("{int}.{frac:0len$}"); // zero-pad to `len`
            let expected =
                int * Quantity::SCALE + frac as u64 * 10_u64.pow(Quantity::PRECISION - len as u32);
            let got = Quantity::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == expected),
                "s={s} expected={expected} got={got:?}"
            );
        }

        // Precision: more than 9 fractional digits must be rejected.
        #[test]
        fn str_rejects_excess_precision(
            int in 0_u64..Quantity::MAX_INTEGER_PART,
            len in (Quantity::PRECISION as usize + 1)..=20_usize,
            seed in any::<u64>(),
        ) {
            let frac: String = (0..len)
                .map(|i| char::from(b'0' + ((seed >> (i % 60)) % 10) as u8))
                .collect();
            let s = format!("{int}.{frac}");
            let got = Quantity::from_str(&s);
            prop_assert!(
                matches!(got, Err(ParseQuantityError::PrecisionError(_))),
                "s={s} got={got:?}"
            );
        }

        // Bounds: an integer part beyond ±MAX_INTEGER_PART must be OutOfBounds
        #[test]
        fn str_rejects_large_integer_part(
            int in (Quantity::MAX_INTEGER_PART + 1)..=(Quantity::MAX_INTEGER_PART + 1000),
        ) {
            let s = format!("{}.0", int);
            let got = Quantity::from_str(&s);
            prop_assert!(
                matches!(got, Err(ParseQuantityError::OutOfBounds)),
                "s={s} got={got:?}"
            );
        }

        // Boundary: integer part == MAX_INTEGER_PART with any fraction
        #[test]
        fn str_accepts_max_integer_with_fraction(
            frac_units in 0_u64..Quantity::SCALE,   // full fractional range
        ) {
            let s = format!("{}.{frac_units:09}", Quantity::MAX_INTEGER_PART);
            let expected = Quantity::MAX_INTEGER_PART * Quantity::SCALE + frac_units;
            let got = Quantity::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == expected),
                "s={s} expected={expected} got={got:?}"
            );
        }
    }
}
