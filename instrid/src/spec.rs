use std::{fmt::Display, num::ParseIntError, ops::Mul, str::FromStr};

use tradeprim::{currency_notional::CurrencyNotional, price::Price, quote_notional::QuoteNotional};

pub trait Specification {
    fn tick_size(&self);
    fn point_value(&self);
}

/// Specification for a futures contract.
///
/// Usually, futures contract has such important values:
/// - Contract Unit - example: 42_000 gallons
/// - Price Quotation   - U.S. dollars and cents per gallon
/// - Minimum Price Fluctuation - 0.0001 per gallon = $4.20
///
/// `4.20 * 1 / 0.0001 = 42_000`
/// `x * 1 / 0.0001 = y` => `0.0001 = x / y`
/// `4.20 * 1 / 0.0001 = y` => `0.0001 = x / y`
///
/// All above - RB@XNYM (NYMEX) contract specification.
///
/// We need this struct to be able to convert `tradeprim::QuoteNotional`
/// to `CurrencyNotional` (which is not implemented yet :) ).
///
/// `currency_notional = quote_notional * point_value`
///
/// Also Price of the instrument should always satisfy such condition:
/// - `price % tick_size == 0` (rounded to the nearest tick size)
///
/// I'm kind of tired to create new types for each data type,
/// but I know that I want both `tick_size` and `point_value`
/// to be like `Quantity`, so... Let's start with it.
///
/// But, I guess, we still need to make it non-negative...
/// Maybe a wrapper? Why not?
pub struct FuturesSpecification {
    /// Usually it is declared as: `(0.0001 per gallon, $4.20)`
    /// We use only first part.
    tick_size: TickSize,
    /// How many tick_sizes' in 1 `point_value`
    tick_quotient: u64, // other values are 8 bytes, so there is no reason to keep it small
    /// A contract multiplier. You multiply QuoteNotional by it and get CurrencyNotional
    point_value: PointValue,
}

impl FuturesSpecification {
    pub fn new(tick_size: TickSize, point_value: PointValue) -> Self {
        let tick_quotient = Price::ONE.value() as u64 / tick_size.0.value().unsigned_abs();

        Self {
            tick_size,
            point_value,
            tick_quotient,
        }
    }

    pub fn tick_size(&self) -> &TickSize {
        &self.tick_size
    }

    pub fn scalar_tick_size(&self) -> Price {
        self.tick_size.0
    }

    pub fn currency_tick_size(&self) -> Price {
        self.tick_size.1
    }

    pub fn point_value(&self) -> PointValue {
        self.point_value
    }

    pub fn tick_quotient(&self) -> u64 {
        self.tick_quotient
    }
}

// ----------------
// --- Wrappers ---
// ----------------
#[derive(Debug)]
pub struct TickSize(Price, Price);

impl TickSize {
    /// Creates a new `TickSize` from a `Price`.
    /// Returns `None` if the price is not positive or greater than 1.
    ///
    /// If `TickSize` is equal to `Price::ONE`, that means that
    /// `PointValue == TickSize` (common case for stock-like instruments)
    pub fn new(scalar: Price, currency: Price) -> Option<Self> {
        if scalar <= Price::ZERO || scalar > Price::ONE {
            return None;
        }
        Some(Self(scalar, currency))
    }
}

impl From<(Price, Price)> for TickSize {
    fn from((scalar, currency): (Price, Price)) -> Self {
        Self::new(scalar, currency).unwrap()
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

impl Mul<QuoteNotional> for PointValue {
    type Output = CurrencyNotional;

    fn mul(self, rhs: QuoteNotional) -> Self::Output {
        CurrencyNotional::new_unchecked(QuoteNotional::round(self.0 * rhs.value()))
    }
}

impl Mul<PointValue> for QuoteNotional {
    type Output = CurrencyNotional;

    fn mul(self, rhs: PointValue) -> Self::Output {
        rhs * self
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

    /// Independent reference for `PointValue * QuoteNotional`
    fn round_ref(v: i128) -> i128 {
        let q = v / PointValue::SCALE; // truncates toward zero
        let r = (v % PointValue::SCALE).abs();
        if r * 2 >= PointValue::SCALE {
            q + v.signum()
        } else {
            q
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
    fn test_point_value_mul_quote_notional() {
        // 1 * 1 = 1
        let pv = PointValue::ONE;
        let qn = QuoteNotional::ONE;
        let result = pv * qn;
        assert_eq!(result, CurrencyNotional::ONE);

        // 10.32 * 2 = 20.64
        let pv = PointValue::from_str_unchecked("10.32");
        let qn = QuoteNotional::from_str_unchecked("2");
        let result = pv * qn;
        assert_eq!(result, CurrencyNotional::new_unchecked(20_640_000_000));
    }

    /// Edgecase: `MAX_RAW * MAX_RAW` (and its negative) lands just
    /// under `i128::MAX`, and `round` adds `SCALE/2` on top.
    #[test]
    fn mul_extremes_do_not_overflow() {
        let pv = PointValue::MAX;
        let qn_max = QuoteNotional::MAX;
        let qn_min = QuoteNotional::MIN;

        let hi = (pv * qn_max).value();
        let lo = (pv * qn_min).value();

        assert_eq!(hi, round_ref(PointValue::MAX_RAW * QuoteNotional::MAX_RAW));
        assert_eq!(lo, round_ref(PointValue::MAX_RAW * QuoteNotional::MIN_RAW));
        // QuoteNotional::MIN_RAW == -MAX_RAW and rounding is odd, so it's symmetric.
        assert_eq!(lo, -hi);
    }

    proptest! {
        /// Check against mul-reference
        #[test]
        fn mul_matches_reference(
            pv_raw in PointValue::MIN_RAW..=PointValue::MAX_RAW,
            qn_raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW,
        ) {
            let pv = PointValue::new(pv_raw).unwrap();
            let qn = QuoteNotional::new(qn_raw).unwrap();
            prop_assert_eq!(
                (pv * qn).value(),
                round_ref(pv_raw * qn_raw),
                "pv_raw={} qn_raw={}", pv_raw, qn_raw
            );
        }

        /// Both `Mul` directions produce the same value.
        #[test]
        fn mul_is_commutative(
            pv_raw in PointValue::MIN_RAW..=PointValue::MAX_RAW,
            qn_raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW,
        ) {
            let pv = PointValue::new(pv_raw).unwrap();
            let qn = QuoteNotional::new(qn_raw).unwrap();
            prop_assert_eq!((pv * qn).value(), (qn * pv).value());
        }

        /// `PointValue::ONE` is the identity
        #[test]
        fn mul_by_one_preserves_quote_raw(
            qn_raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW,
        ) {
            let qn = QuoteNotional::new(qn_raw).unwrap();
            prop_assert_eq!((PointValue::ONE * qn).value(), qn_raw);
        }

        /// With a strictly positive point value, the result's sign tracks the
        /// quote notional's sign (zero maps to zero).
        #[test]
        fn mul_sign_follows_quote(
            pv_raw in 1..=PointValue::MAX_RAW,
            qn_raw in QuoteNotional::MIN_RAW..=QuoteNotional::MAX_RAW,
        ) {
            let pv = PointValue::new(pv_raw).unwrap();
            let qn = QuoteNotional::new(qn_raw).unwrap();
            prop_assert_eq!((pv * qn).value().signum(), round_ref(pv_raw * qn_raw).signum());
        }
    }
}
