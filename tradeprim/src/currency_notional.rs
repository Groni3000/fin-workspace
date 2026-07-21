use crate::price::Price;

/// Has fixed scale and max value.
///
/// Pretty similar to `QuoteNotional`.
///
/// `CurrencyNotional` is usually a result of multiplication of `QuoteNotional` by `PointValue`.
///
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CurrencyNotional {
    value: i128,
}

impl CurrencyNotional {
    pub const SCALE: i128 = Price::SCALE as i128;

    pub const ONE: Self = Self::new_unchecked(Self::SCALE);
    pub const ZERO: Self = Self::new_unchecked(0_i128);

    pub const fn new(value: i128) -> Self {
        Self { value }
    }

    pub const fn new_unchecked(value: i128) -> Self {
        Self { value }
    }

    pub fn value(&self) -> i128 {
        self.value
    }
}
