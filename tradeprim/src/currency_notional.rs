/// Has fixed scale and max value.
///
/// Pretty similar to `QuoteNotional`.
///
/// `CurrencyNotional` is usually a result of multiplication of `QuoteNotional` by `PointValue`.
///
#[derive(Debug, Clone, Copy)]
pub struct CurrencyNotional {
    value: i128,
}

impl CurrencyNotional {
    pub fn new(value: i128) -> Self {
        Self { value }
    }

    pub fn value(&self) -> i128 {
        self.value
    }
}
