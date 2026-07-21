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

#[derive(Debug, Clone, Copy)]
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
    pub const MIN_RAW: i128 = i128::MIN / QuoteNotional::MAX_RAW;
    pub const MAX_INTEGER_PART: i128 = Self::MAX_RAW / Self::SCALE;
    pub const MIN_INTEGER_PART: i128 = Self::MIN_RAW / Self::SCALE;

    pub const ONE: i128 = Self::SCALE;
    pub const ZERO: i128 = 0;

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
        if !(Self::ZERO..=Self::MAX_RAW).contains(&value) {
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
        if fraction.starts_with('-') {
            return Err(ParsePointValueError::InvalidFormat);
        }
        let is_negative = integer.starts_with('-');

        let parsed_integer =
            i128::from_str(integer).map_err(ParsePointValueError::ParseIntError)?;
        if !(-Self::MAX_INTEGER_PART..=Self::MAX_INTEGER_PART).contains(&parsed_integer) {
            return Err(ParsePointValueError::OutOfBounds);
        }
        // We do it after min/max check because i128::MIN.abs() would panic
        let parsed_integer = parsed_integer.abs();

        let used_precision = fraction.len();
        if used_precision > Self::PRECISION as usize {
            return Err(ParsePointValueError::PrecisionError(used_precision));
        }
        let remaining_precision = Self::PRECISION - used_precision as u32;
        let parsed_fraction =
            i128::from_str(fraction).map_err(ParsePointValueError::ParseIntError)?;
        let adjusted_fraction = parsed_fraction * Self::POW10[remaining_precision as usize];

        let combined = match is_negative {
            true => -(parsed_integer * Self::SCALE + adjusted_fraction),
            false => parsed_integer * Self::SCALE + adjusted_fraction,
        };

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
        CurrencyNotional::new((self.0 * Self::SCALE) * rhs.value())
    }
}

impl Mul<PointValue> for QuoteNotional {
    type Output = CurrencyNotional;

    fn mul(self, rhs: PointValue) -> Self::Output {
        rhs * self
    }
}
