use std::{fmt::Display, num::ParseIntError, str::FromStr};

/// Has fixed scale and max value.
///
/// Initially, I thought to do something like this:
/// - Price - Price -> PriceDelta<i64>
/// - Price * Quantity<u64> -> Notional<i128?>
/// - Price / Price -> f64
/// - Price + Price -> NotImplemented (no sense?)
///
/// But for now, no math operations are implemented.
/// For now this struct can be used for retrieving price values from the API or sending orders.
/// Though `Notional` is probably gonna be implemented in the end.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Price {
    value: i64,
}

impl Price {
    pub const PRECISION: u32 = 9;
    /// 1e9
    pub const SCALE: i64 = 10_i64.pow(Price::PRECISION);
    /// 1e6
    pub const MAX_INTEGER_PART: i64 = 1_000_000;
    /// 1_000_000.999_999_999 (max integer part with a full fraction)
    pub const MAX_RAW: i64 = Price::MAX_INTEGER_PART * Price::SCALE + (Price::SCALE - 1);
    /// -1_000_000.999_999_999
    pub const MIN_RAW: i64 = -Price::MAX_RAW;
    /// zero value
    pub const ZERO: Self = Self { value: 0 };

    pub fn new(value: i64) -> Option<Self> {
        if value > Self::MAX_RAW || value < Self::MIN_RAW {
            return None;
        }

        Some(Self { value })
    }

    fn new_unchecked(value: i64) -> Self {
        Self { value }
    }

    pub fn value(self) -> i64 {
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

        let parsed_integer = i64::from_str(integer).unwrap().abs();

        let used_precision = fraction.len();
        let remaining_precision = Price::PRECISION - used_precision as u32;
        let parsed_fraction = i64::from_str(fraction).unwrap();
        // Powers of ten indexed by remaining precision (0..=PRECISION), so the
        // per-parse scaling is a table lookup instead of a runtime `pow`.
        const POW10: [i64; Price::PRECISION as usize + 1] = [
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
        let adjusted_fraction = parsed_fraction * POW10[remaining_precision as usize];

        let combined = match is_negative {
            true => -(parsed_integer * Price::SCALE + adjusted_fraction),
            false => parsed_integer * Price::SCALE + adjusted_fraction,
        };

        Price::new_unchecked(combined)
    }
}

impl Display for Price {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value as f64 / Price::SCALE as f64)
    }
}

impl From<Price> for f64 {
    fn from(value: Price) -> Self {
        value.value as f64 / Price::SCALE as f64
    }
}

impl From<Price> for i64 {
    fn from(value: Price) -> Self {
        value.value
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParsePriceError {
    InvalidFormat,
    OutOfBounds,
    PrecisionError(usize),
    ParseIntError(ParseIntError),
}

impl FromStr for Price {
    type Err = ParsePriceError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, "000000000"));
        let (integer, fraction) = (integer.trim(), fraction.trim());
        // Check below needed to not accept and parse `-0.-1`
        // The fraction part would be parsed no problem
        if fraction.starts_with('-') {
            return Err(ParsePriceError::InvalidFormat);
        }
        let is_negative = integer.starts_with('-');

        let parsed_integer = i64::from_str(integer).map_err(ParsePriceError::ParseIntError)?;
        if parsed_integer > Price::MAX_INTEGER_PART || parsed_integer < -Price::MAX_INTEGER_PART {
            return Err(ParsePriceError::OutOfBounds);
        }
        // We do it after min/max check because i64::MIN.abs() would panic
        let parsed_integer = parsed_integer.abs();

        let used_precision = fraction.len();
        if used_precision > Price::PRECISION as usize {
            return Err(ParsePriceError::PrecisionError(used_precision));
        }
        let remaining_precision = Price::PRECISION - used_precision as u32;
        let parsed_fraction = i64::from_str(fraction).map_err(ParsePriceError::ParseIntError)?;
        // Powers of ten indexed by remaining precision (0..=PRECISION), so the
        // per-parse scaling is a table lookup instead of a runtime `pow`.
        const POW10: [i64; Price::PRECISION as usize + 1] = [
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
        let adjusted_fraction = parsed_fraction * POW10[remaining_precision as usize];

        let combined = match is_negative {
            true => -(parsed_integer * Price::SCALE + adjusted_fraction),
            false => parsed_integer * Price::SCALE + adjusted_fraction,
        };

        Ok(Price::new_unchecked(combined))
    }
}

/// Errors that can occur when converting a `f64` to a `Price`.
/// f64 field is the original value that caused the fail
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum FromF64Error {
    OutOfBounds(f64),
}

impl TryFrom<f64> for Price {
    type Error = FromF64Error;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        if !value.is_finite() {
            return Err(FromF64Error::OutOfBounds(value));
        }
        let raw = (value * Price::SCALE as f64).round() as i64;
        Self::new(raw).ok_or_else(|| FromF64Error::OutOfBounds(value))
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
    fn test_price_new() {
        let max_price = Price::new(Price::MAX_RAW).unwrap();
        assert_eq!(Price::MAX_RAW, max_price.value);

        let min_price = Price::new(Price::MIN_RAW).unwrap();
        assert_eq!(Price::MIN_RAW, min_price.value);

        assert!(Price::new(Price::MAX_RAW + 1).is_none());
        assert!(Price::new(Price::MIN_RAW - 1).is_none());
    }

    #[test]
    fn test_f64_to_price_conversions() {
        let raw = 65537.273030587;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == 65537_273_030_587));

        // --- Normal cases
        let raw = 100.0;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == 100_000_000_000));

        let raw = -100.0;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == -100_000_000_000));

        let raw = 0.000000015;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == 000_000_015));

        let raw = 100.239;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == 100_239_000_000));

        let raw = -100.239;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == -100_239_000_000));

        // --- Edge cases (MAX/MIN/ZERO/signed smallest non-zero)
        let raw = 1_000_000.0;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == 1_000_000_000_000_000));

        let raw = -1_000_000.0;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == -1_000_000_000_000_000));

        let raw = 0.0;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == 0));

        let raw = 0.000000001;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == 1));

        let raw = -0.000000001;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == -1));

        // --- Error cases (too large/precision loss)
        let raw = 0.0000000001; // 1 digit out of precision
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x == Price::ZERO));

        let raw = -0.0000000001;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x == Price::ZERO));

        let raw = 0.000000000001; // 0.001 - 3 digits out of precision
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x == Price::ZERO));

        let raw = 0.0000000000001; // 0.0001 - Should not cause an error
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x == Price::ZERO));

        let raw = 0.000_000_000_000_9; // 0.0009 - Should not cause an error
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x == Price::ZERO));

        let raw = 1_000_001.0; // out of bound by 1 unit
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));

        let raw = -1_000_001.0;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));

        let raw = 1_000_000.000000001;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == 1_000_000_000_000_001));

        let raw = -1_000_000.000000001;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x.value == -1_000_000_000_000_001));

        // NAN/INF/NEG_INF
        let raw = f64::NAN;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));

        let raw = f64::INFINITY;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));

        let raw = f64::NEG_INFINITY;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));
    }

    #[test]
    fn test_price_to_f64_conversions() {
        let price = Price::new(0_999_999_999_999_999);
        assert!(price.is_some_and(|x| {
            let raw_price: f64 = x.into();
            let expected_price = 999_999.999_999_999_f64;
            raw_price.total_cmp(&expected_price) == Ordering::Equal
        }));

        let price = Price::new(0_999_999_000_000_099);
        assert!(price.is_some_and(|x| {
            let raw_price: f64 = x.into();
            let expected_price = 999_999.000_000_099_f64;
            raw_price.total_cmp(&expected_price) == Ordering::Equal
        }));

        let price = Price::new(0_000_000_000_000_099);
        assert!(price.is_some_and(|x| {
            let raw_price: f64 = x.into();
            let expected_price = 0.000_000_099_f64;
            raw_price.total_cmp(&expected_price) == Ordering::Equal
        }));
    }

    #[test]
    fn test_str_to_price_conversions() {
        let input = "";
        let price = Price::from_str(input);
        assert_matches!(price, Err(ParsePriceError::ParseIntError(_)));

        let input = "1";
        let price = Price::from_str(input);
        assert!(price.is_ok_and(|x| x.eq(&Price::new_unchecked(1_000_000_000))));

        let input = "1.0";
        let price = Price::from_str(input);
        assert!(price.is_ok_and(|x| x.eq(&Price::new_unchecked(1_000_000_000))));

        let input = "-1.0";
        let price = Price::from_str(input);
        assert!(price.is_ok_and(|x| x.eq(&Price::new_unchecked(-1_000_000_000))));

        let input = "-0.5";
        let price = Price::from_str(input);
        assert!(price.is_ok_and(|x| x.eq(&Price::new_unchecked(-500_000_000))));

        let input = "1.5";
        let price = Price::from_str(input);
        assert!(price.is_ok_and(|x| x.eq(&Price::new_unchecked(1_500_000_000))));

        let input = "1.-5";
        let price = Price::from_str(input);
        assert_matches!(price, Err(ParsePriceError::InvalidFormat));
    }

    proptest! {
        #[test]
        fn is_some_for_small_integers(s in (-10_i64..10_i64)) {
            assert!(Price::new(s).is_some());
        }

        #[test]
        fn is_some_for_large_positive_integers(s in (Price::MAX_RAW - 10)..=Price::MAX_RAW) {
            assert!(Price::new(s).is_some());
        }

        #[test]
        fn is_none_for_large_positive_integers(s in (Price::MAX_RAW + 1)..=(Price::MAX_RAW + 11)) {
            assert!(Price::new(s).is_none());
        }

        #[test]
        fn is_some_for_large_negative_integers(s in Price::MIN_RAW..=(Price::MIN_RAW + 10)) {
            assert!(Price::new(s).is_some());
        }

        #[test]
        fn is_none_for_large_negative_integers(s in (Price::MIN_RAW - 11)..=(Price::MIN_RAW - 1)) {
            assert!(Price::new(s).is_none());
        }
    }

    proptest! {
        // Normal case: every in-range raw value, turned into an f64 price and
        // parsed back, must recover the exact same raw. (NAN/INF are covered by
        // the unit test above.)
        #[test]
        fn f64_roundtrips_for_in_range_raw(raw in Price::MIN_RAW..=Price::MAX_RAW) {
            let v = raw as f64 / Price::SCALE as f64;
            let got = Price::try_from(v);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == raw),
                "v={v} raw={raw} got={got:?}"
            );
        }

        // OutOfBounds: whole-number magnitudes just past ±1e6. Kept small enough
        // that `major * SCALE` is an exact f64 integer, so the only reason to
        // reject is the bounds check (not precision).
        #[test]
        fn out_of_bounds_for_large_magnitude(major in 1_000_001_i64..=2_000_000_i64) {
            for v in [major as f64, -(major as f64)] {
                let got = Price::try_from(v);
                prop_assert!(
                    matches!(got, Err(FromF64Error::OutOfBounds(_))),
                    "v={v} got={got:?}"
                );
            }
        }
    }

    // Canonical decimal string for a raw value: always 9 fractional digits.
    fn raw_to_decimal_string(raw: i64) -> String {
        let sign = if raw < 0 { "-" } else { "" };
        let a = raw.unsigned_abs();
        let int = a / Price::SCALE as u64;
        let frac = a % Price::SCALE as u64;
        format!("{sign}{int}.{frac:09}")
    }

    proptest! {
        #[test]
        fn str_for_in_range_raw(raw in Price::MIN_RAW..=Price::MAX_RAW) {
            let s = raw_to_decimal_string(raw);
            let got = Price::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == raw),
                "s={s} raw={raw} got={got:?}"
            );
        }

        // Correct scaling: 0.5 -> 500_000_000
        #[test]
        fn str_scales_fraction_by_position(
            neg in any::<bool>(),
            int in 0_i64..Price::MAX_INTEGER_PART,
            len in 1_usize..=Price::PRECISION as usize,
            seed in 0_u64..Price::SCALE as u64,
        ) {
            let frac = seed % 10_u64.pow(len as u32); // fits in `len` digits
            let sign = if neg { "-" } else { "" };
            let s = format!("{sign}{int}.{frac:0len$}"); // zero-pad to `len`
            let magnitude =
                int * Price::SCALE + frac as i64 * 10_i64.pow(Price::PRECISION - len as u32);
            let expected = if neg { -magnitude } else { magnitude };
            let got = Price::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == expected),
                "s={s} expected={expected} got={got:?}"
            );
        }

        // Precision: more than 9 fractional digits must be rejected.
        #[test]
        fn str_rejects_excess_precision(
            int in 0_i64..Price::MAX_INTEGER_PART,
            len in (Price::PRECISION as usize + 1)..=20_usize,
            seed in any::<u64>(),
        ) {
            let frac: String = (0..len)
                .map(|i| char::from(b'0' + ((seed >> (i % 60)) % 10) as u8))
                .collect();
            let s = format!("{int}.{frac}");
            let got = Price::from_str(&s);
            prop_assert!(
                matches!(got, Err(ParsePriceError::PrecisionError(_))),
                "s={s} got={got:?}"
            );
        }

        // Bounds: an integer part beyond ±MAX_INTEGER_PART must be OutOfBounds
        #[test]
        fn str_rejects_large_integer_part(
            int in (Price::MAX_INTEGER_PART + 1)..=1_000_000_000_i64,
            neg in any::<bool>(),
        ) {
            let s = format!("{}{int}.0", if neg { "-" } else { "" });
            let got = Price::from_str(&s);
            prop_assert!(
                matches!(got, Err(ParsePriceError::OutOfBounds)),
                "s={s} got={got:?}"
            );
        }

        // Boundary: integer part == MAX_INTEGER_PART with any fraction
        #[test]
        fn str_accepts_max_integer_with_fraction(
            neg in any::<bool>(),
            frac_units in 0_i64..Price::SCALE,   // full fractional range
        ) {
            let sign = if neg { "-" } else { "" };
            let s = format!("{sign}{}.{frac_units:09}", Price::MAX_INTEGER_PART);
            let magnitude = Price::MAX_INTEGER_PART * Price::SCALE + frac_units;
            let expected = if neg { -magnitude } else { magnitude };
            let got = Price::from_str(&s);
            prop_assert!(
                matches!(got, Ok(p) if p.value() == expected),
                "s={s} expected={expected} got={got:?}"
            );
        }
    }
}
