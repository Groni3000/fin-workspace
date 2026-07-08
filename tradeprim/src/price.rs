use std::fmt::Display;

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
    /// 1e9
    pub const SCALE: i64 = 1_000_000_000;
    /// 1e6 (real), 1e9 (Scale)
    pub const MAX_RAW: i64 = 1_000_000_000_000_000;
    /// 1e6 (real), 1e9 (Scale)
    pub const MIN_RAW: i64 = -1_000_000_000_000_000;
    /// zero value
    pub const ZERO: Self = Self { value: 0 };

    pub fn new(value: i64) -> Option<Self> {
        if value > Self::MAX_RAW || value < Self::MIN_RAW {
            return None;
        }

        Some(Self { value })
    }

    pub fn value(self) -> i64 {
        self.value
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
        let max_raw_price = 1_000_000_000_000_000;
        let max_price = Price::new(max_raw_price).unwrap();
        assert_eq!(Price::MAX_RAW, max_price.value);

        let min_raw_price = -1_000_000_000_000_000;
        let min_price = Price::new(min_raw_price).unwrap();
        assert_eq!(Price::MIN_RAW, min_price.value);

        let invalid_price = 1_000_000_000_000_001;
        assert!(Price::new(invalid_price).is_none());
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

        // closest to threshold of 0.001
        let raw = 0.000_000_000_000_9; // 0.0009 - Should not cause an error
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert!(price.is_ok_and(|x| x == Price::ZERO));

        let raw = 1_000_001.0; // out of bound by 1 unit
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));

        let raw = -1_000_001.0;
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));

        let raw = 1_000_000.000000001; // out of bound by 1 digit
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));

        let raw = -1_000_000.000000001; // out of bound by 1 digit
        let price: Result<Price, FromF64Error> = TryInto::try_into(raw);
        assert_matches!(price, Err(FromF64Error::OutOfBounds(_)));

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

    proptest! {
        #[test]
        fn is_some_for_small_integers(s in (-10_i64..10_i64)) {
            assert!(Price::new(s).is_some());
        }

        #[test]
        fn is_some_for_large_positive_integers(s in (0_999_999_999_999_990_i64..1_000_000_000_000_001_i64)) {
            assert!(Price::new(s).is_some());
        }

        #[test]
        fn is_none_for_large_positive_integers(s in (1_000_000_000_000_001_i64..1_000_000_000_000_011_i64)) {
            assert!(Price::new(s).is_none());
        }

        #[test]
        fn is_some_for_large_negative_integers(s in (-1_000_000_000_000_000_i64..-0_999_999_999_999_990_i64)) {
            assert!(Price::new(s).is_some());
        }

        #[test]
        fn is_none_for_large_negative_integers(s in (-1_000_000_000_000_011_i64..=-1_000_000_000_000_001_i64)) {
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
}
