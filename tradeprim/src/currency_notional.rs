use crate::{currency::Currency, price::Price};

/// Has fixed scale and max value.
///
/// Pretty similar to `QuoteNotional`.
///
/// `CurrencyNotional` is usually a result of multiplication of `QuoteNotional` by `PointValue`.
///
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CurrencyNotional {
    value: i128,
    currency: Currency,
}

impl CurrencyNotional {
    pub const SCALE: i128 = Price::SCALE as i128;

    pub const ONE_RAW: i128 = Self::SCALE;
    pub const ZERO_RAW: i128 = 0_i128;

    pub const fn new(value: i128, currency: Currency) -> Self {
        Self { value, currency }
    }

    pub const fn new_unchecked(value: i128, currency: Currency) -> Self {
        Self { value, currency }
    }

    pub fn value(&self) -> i128 {
        self.value
    }
}
