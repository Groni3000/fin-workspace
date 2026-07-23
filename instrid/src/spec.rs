use std::{fmt::Display, num::ParseIntError, str::FromStr};

use tradeprim::{currency::Currency, price::Price, quote_notional::QuoteNotional};

/// Has essential trading specification parameters.
///
pub trait Spec {
    fn tick_size_price(&self) -> Price;
    fn tick_size_currency(&self) -> (Price, Currency);
    fn point_value(&self) -> PointValue;
}

/// Represents the essential trading specification parameters.
#[derive(Debug, Clone, PartialEq)]
pub struct Specification {
    tick_size_price: Price,
    tick_size_currency: (Price, Currency),
    point_value: PointValue,
}

impl Default for Specification {
    fn default() -> Self {
        Self {
            tick_size_price: Price::from_str_unchecked("0.01"),
            tick_size_currency: (Price::from_str_unchecked("0.01"), Currency::default()),
            point_value: PointValue::ONE,
        }
    }
}

impl Specification {
    /// Builds a `Specification`, deriving `point_value` from the tick pair as
    /// `tick_size_currency.0 / tick_size_price`.
    ///
    /// # **Error-prone**: units are NOT verifiable
    ///
    /// Let's say that Currency has 2 forms: major and minor.
    /// We usually use major form: 2.13 ($)
    /// Minor form would use cents: 213 (cents)
    ///
    /// Usually `tick_size_currency` is in major form. At least I haven't seen
    /// a case where it's in minor form.
    ///
    /// But `tick_size_price` is in price quotation units and if price quotation in
    /// minor form - it should be in minor form. But, unfortunately, at least CME,
    /// can sometimes convert it to major form.
    ///
    /// Example of such case:
    /// - ZW - CME spec says its `tick_size_price` is 1/4 of a cent and write 0.0025
    ///     and you may think that you can just copy-paste its value like you do with other
    ///     futures contracts. But no, 1/4 of a cent is 0.25, but CME shows 0.0025 which is in major
    ///     form - wrong one, price is in minor.
    ///     So we should use 0.25. For an explanation, look at README.md, ZW example.
    ///     So the correct values are:
    ///     `(0.25, (12.5, USD))` - you can't copy-paste values from CME specification.
    ///
    /// So, fill a spec **once**, verify by hand and reuse specs.
    pub fn new(tick_size_price: Price, tick_size_currency: (Price, Currency)) -> Option<Self> {
        if tick_size_price <= Price::ZERO || tick_size_price > Price::ONE {
            return None;
        }
        let point_value = PointValue::new(
            (tick_size_currency.0.value() as i128 * PointValue::SCALE)
                / tick_size_price.value() as i128,
        )?;
        Some(Self {
            tick_size_price,
            tick_size_currency,
            point_value,
        })
    }
}

impl Spec for Specification {
    fn tick_size_price(&self) -> Price {
        self.tick_size_price
    }

    fn tick_size_currency(&self) -> (Price, Currency) {
        self.tick_size_currency
    }

    fn point_value(&self) -> PointValue {
        self.point_value
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PointValue(i128);

impl PointValue {
    pub const SCALE: i128 = Price::SCALE as i128;
    pub const PRECISION: u32 = Price::PRECISION;
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
    /// Max reference: JPY futures = 12.5 mil
    /// ```
    /// use tradeprim::quote_notional::QuoteNotional;
    ///
    /// pub const MAX_RAW: i128 = i128::MAX / QuoteNotional::MAX_RAW;
    /// assert_eq!(MAX_RAW, 34028195858252051);
    /// ```
    pub const MAX_RAW: i128 = i128::MAX / QuoteNotional::MAX_RAW;
    pub const MIN_RAW: i128 = 1_i128;
    pub const MAX_INTEGER_PART: i128 = Self::MAX_RAW / Self::SCALE;
    pub const MIN_INTEGER_PART: i128 = Self::MIN_RAW / Self::SCALE;

    pub const ONE: Self = Self::new_unchecked(Self::SCALE);
    pub const MAX: Self = Self::new_unchecked(Self::MAX_RAW);
    pub const MIN: Self = Self::new_unchecked(Self::MIN_RAW);

    /// Creates a new `PointValue` from a `Price`.
    /// Returns `None` if the price is not positive or greater than
    /// some reasonable amount.
    ///
    /// If `TickSize` is equal to `Price::ONE`, that means that
    /// `PointValue == TickSize` (common case for stock-like instruments)
    ///
    /// It's hard to argue about the maximum value of `PointValue`.
    /// For example, there is a JPY futures with point value of 12.5mil
    pub fn new(value: i128) -> Option<Self> {
        if !(Self::MIN_RAW..=Self::MAX_RAW).contains(&value) {
            return None;
        }
        Some(Self(value))
    }

    pub fn value(&self) -> i128 {
        self.0
    }

    const fn new_unchecked(value: i128) -> Self {
        Self(value)
    }

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
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParsePointValueError {
    InvalidFormat,
    OutOfBounds,
    PrecisionError(usize),
    ParseIntError(ParseIntError),
}

impl Display for ParsePointValueError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParsePointValueError::InvalidFormat => write!(f, "Invalid format"),
            ParsePointValueError::OutOfBounds => write!(f, "Out of bounds"),
            ParsePointValueError::PrecisionError(precision) => {
                write!(f, "Precision error: {}", precision)
            }
            ParsePointValueError::ParseIntError(err) => err.fmt(f),
        }
    }
}

// --- Basically a copy-paste from a Price
impl FromStr for PointValue {
    type Err = ParsePointValueError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, "000000000"));
        let (integer, fraction) = (integer.trim(), fraction.trim());
        // Check below needed to not accept and parse `-0.-1`
        // The fraction part would be parsed no problem
        if fraction.starts_with('-') || integer.starts_with('-') {
            return Err(ParsePointValueError::InvalidFormat);
        }

        let parsed_integer =
            i128::from_str(integer).map_err(ParsePointValueError::ParseIntError)?;
        if !(0..=Self::MAX_INTEGER_PART).contains(&parsed_integer) {
            return Err(ParsePointValueError::OutOfBounds);
        }

        let used_precision = fraction.len();
        if used_precision > Self::PRECISION as usize {
            return Err(ParsePointValueError::PrecisionError(used_precision));
        }
        let remaining_precision = Self::PRECISION - used_precision as u32;
        let parsed_fraction =
            i128::from_str(fraction).map_err(ParsePointValueError::ParseIntError)?;
        let adjusted_fraction = parsed_fraction * Self::POW10[remaining_precision as usize];
        let combined = parsed_integer * Self::SCALE + adjusted_fraction;
        if !(Self::MIN_RAW..=Self::MAX_RAW).contains(&combined) {
            return Err(ParsePointValueError::OutOfBounds);
        }

        Ok(Self::new_unchecked(combined))
    }
}

impl From<i128> for PointValue {
    fn from(value: i128) -> Self {
        Self::new(value).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::assert_matches;

    /// Canonical string for a non-negative `PointValue` raw value.
    fn pv_canonical(raw: i128) -> String {
        let int = raw / PointValue::SCALE;
        let frac = raw % PointValue::SCALE;
        if frac == 0 {
            format!("{int}")
        } else {
            format!("{int}.{}", format!("{frac:09}").trim_end_matches('0'))
        }
    }

    #[test]
    fn test_point_value_init() {
        assert!(PointValue::new(PointValue::MIN_RAW).is_some());
        assert!(PointValue::new(PointValue::MIN_RAW - 1).is_none());
        assert!(PointValue::new(PointValue::MAX_RAW).is_some());
        assert!(PointValue::new(PointValue::MAX_RAW + 1).is_none());
        assert!(
            PointValue::from_str("100")
                .is_ok_and(|x| x == PointValue::new_unchecked(100 * PointValue::SCALE))
        );
        assert!(
            PointValue::from_str("100.000000001")
                .is_ok_and(|x| x == PointValue::new_unchecked(100 * PointValue::SCALE + 1))
        );
        // --- Errors paths
        assert!(
            PointValue::from_str("-100").is_err_and(|x| x == ParsePointValueError::InvalidFormat)
        );
        assert_matches!(
            PointValue::from_str("1a.32").expect_err("Should fail with ParseIntError"),
            ParsePointValueError::ParseIntError(_)
        );
        assert_matches!(
            PointValue::from_str("10.3a").expect_err("Should fail with ParseIntError"),
            ParsePointValueError::ParseIntError(_)
        );
        assert!(
            PointValue::from_str("-100.000000001")
                .is_err_and(|x| x == ParsePointValueError::InvalidFormat)
        );
        let max_integer_part = (PointValue::MAX_INTEGER_PART + 1).to_string();
        assert!(
            PointValue::from_str(&max_integer_part)
                .is_err_and(|x| x == ParsePointValueError::OutOfBounds)
        );
        assert!(
            PointValue::from_str("100.0000000001")
                .is_err_and(|x| x == ParsePointValueError::PrecisionError(10))
        );
    }

    /// Zero is not a valid contract multiplier: `from_str` rejects it
    #[test]
    fn from_str_rejects_zero() {
        for s in ["0", "0.0", "0.000000000"] {
            assert_eq!(
                PointValue::from_str(s),
                Err(ParsePointValueError::OutOfBounds),
                "from_str({s:?}) must reject a zero point value"
            );
        }
    }

    #[test]
    fn from_str_accepts_endpoints() {
        // MIN_RAW == 1 raw == 0.000000001 (smallest strictly-positive value).
        let min = PointValue::from_str("0.000000001").expect("MIN_RAW must parse");
        assert_eq!(min.value(), PointValue::MIN_RAW);

        // MAX_RAW rendered canonically must round-trip exactly.
        let max =
            PointValue::from_str(&pv_canonical(PointValue::MAX_RAW)).expect("MAX_RAW must parse");
        assert_eq!(max.value(), PointValue::MAX_RAW);
    }

    #[test]
    fn from_str_rejects_above_max() {
        let s = format!("{}.999999999", PointValue::MAX_INTEGER_PART);
        assert_eq!(
            PointValue::from_str(&s),
            Err(ParsePointValueError::OutOfBounds),
            "from_str({s:?}) is above MAX_RAW"
        );
    }

    proptest! {
        /// Every in-range raw value roundtrips through `from_str`.
        #[test]
        fn from_str_roundtrips_in_range(raw in PointValue::MIN_RAW..=PointValue::MAX_RAW) {
            let s = pv_canonical(raw);
            prop_assert!(
                matches!(PointValue::from_str(&s), Ok(p) if p.value() == raw),
                "raw={raw} s={s}"
            );
        }

        /// Similar to `from_str_rejects_above_max`, but proptest
        #[test]
        fn from_str_rejects_overshoot_fraction(
            frac in (PointValue::MAX_RAW % PointValue::SCALE + 1)..PointValue::SCALE,
        ) {
            let s = format!("{}.{frac:09}", PointValue::MAX_INTEGER_PART);
            prop_assert_eq!(
                PointValue::from_str(&s),
                Err(ParsePointValueError::OutOfBounds),
                "s={}", s
            );
        }
    }

    #[test]
    fn specification_tests() {
        // default case for a common shares
        // usd, cents
        let ts_p = Price::from_str_unchecked("0.01");
        let ts_c = (Price::from_str_unchecked("0.01"), Currency::default());
        let spec = Specification::new(ts_p, ts_c).unwrap();
        assert_eq!(ts_p, spec.tick_size_price());
        assert_eq!(ts_c.0, spec.tick_size_currency().0);
        assert_eq!(PointValue::from_str_unchecked("1.0"), spec.point_value());
        assert_eq!(spec.tick_size_currency.1, Currency::usd());

        // ZW, 5k bushels, price in cents, tick_size_currency in $
        // I had to multiply 0.0025 by 100...
        let spec = Specification::new(
            Price::from_str_unchecked("0.25"),
            (Price::from_str_unchecked("12.5"), Currency::usd()),
        )
        .unwrap();
        assert_eq!(Price::from_str_unchecked("0.25"), spec.tick_size_price());
        assert_eq!(
            Price::from_str_unchecked("12.5"),
            spec.tick_size_currency().0
        );
        assert_eq!(PointValue::from_str_unchecked("50.0"), spec.point_value());

        // RB, 42k gallons, price in dollars and cents, tick_size_currency in $
        let spec = Specification::new(
            Price::from_str_unchecked("0.0001"),
            (Price::from_str_unchecked("4.2"), Currency::usd()),
        )
        .unwrap();
        assert_eq!(Price::from_str_unchecked("0.0001"), spec.tick_size_price());
        assert_eq!(
            Price::from_str_unchecked("4.2"),
            spec.tick_size_currency().0
        );
        assert_eq!(
            PointValue::from_str_unchecked("42000.0"),
            spec.point_value()
        );

        // ZB, Face value at maturity of $100,000,
        // price Points and fractions of points with par on the basis of 100 points,
        // tick_size_currency in $
        let spec = Specification::new(
            Price::from_str_unchecked("0.03125"),
            (Price::from_str_unchecked("31.25"), Currency::usd()),
        )
        .unwrap();
        assert_eq!(Price::from_str_unchecked("0.03125"), spec.tick_size_price());
        assert_eq!(
            Price::from_str_unchecked("31.25"),
            spec.tick_size_currency().0
        );
        assert_eq!(PointValue::from_str_unchecked("1000.0"), spec.point_value());

        // 6J, contract_unit = 12,500,000 Japanese yen,
        // price U.S. dollars and cent per JPY increment,
        // 0.0000005 per JPY increment = $6.25
        let spec = Specification::new(
            Price::from_str_unchecked("0.0000005"),
            (Price::from_str_unchecked("6.25"), Currency::usd()),
        )
        .unwrap();
        assert_eq!(
            Price::from_str_unchecked("0.0000005"),
            spec.tick_size_price()
        );
        assert_eq!(
            Price::from_str_unchecked("6.25"),
            spec.tick_size_currency().0
        );
        assert_eq!(
            PointValue::from_str_unchecked("12500000.0"),
            spec.point_value()
        );
    }

    /// - `tick_size_price` is in `(0, Price::ONE)`
    /// - `tick_size_price` that is `Price::ONE` accepted
    /// - `tick_size_price = Price::ONE + min increment` - not accepted
    #[test]
    fn new_tick_size_price_boundary() {
        let usd = (Price::ONE, Currency::usd());

        // Below the range: zero tick would divide by zero deriving point_value.
        assert!(
            Specification::new(Price::ZERO, usd).is_none(),
            "tick_size_price = 0 must be rejected"
        );

        // Upper edge is inclusive: exactly one whole price unit is valid.
        assert!(
            Specification::new(Price::ONE, usd).is_some(),
            "tick_size_price == Price::ONE must be accepted"
        );

        // One raw step above the edge: not a valid tick.
        let above_one = Price::from_str_unchecked("1.000000001");
        assert!(
            Specification::new(above_one, usd).is_none(),
            "tick_size_price > Price::ONE must be rejected"
        );
    }
}
