use std::ops::Mul;

use tradeprim::{currency_notional::CurrencyNotional, price::Price, quote_notional::QuoteNotional};

pub trait Specification {
    fn tick_size(&self);
    fn point_value(&self);
}

/// Specification for a futures contract.
///
/// Usually, futures contract has such important values:
/// - Contract Unit	- example: 42_000 gallons
/// - Price Quotation - U.S. dollars and cents per gallon
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
        let tick_quotient = Price::ONE.value() as u64 / tick_size.0.value().abs() as u64;

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
    /// Max reference: JPY futures = 12.5 mil
    pub const MAX: i128 = 12_500_000_000_000_000;
    pub const MIN: i128 = 0;

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
        if value < Self::ZERO || value > Self::MAX {
            return None;
        }
        Some(Self(value))
    }

    pub fn value(&self) -> i128 {
        self.0
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
