#![doc = include_str!("../README.md")]

pub mod ascii_code;
pub mod currency;
pub mod currency_notional;
pub mod decimal;
pub mod position;
pub mod price;
pub mod quantity;
pub mod quote_notional;
pub mod volume;

use std::ops::Neg;

pub mod prelude {
    pub use crate::Side;
    pub use crate::currency::{Currency, CurrencyTag};
    pub use crate::price::Price;
    pub use crate::quantity::Quantity;
    pub use crate::volume::Volume;

    pub mod errors {
        pub use crate::ascii_code::AsciiCode;
        pub use crate::decimal::ParseDecimalError;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Side {
    Buy,
    Sell,
}

impl Side {
    pub fn opposite(self) -> Self {
        match self {
            Self::Buy => Self::Sell,
            Self::Sell => Self::Buy,
        }
    }

    pub fn as_i64(self) -> i64 {
        match self {
            Self::Buy => 1,
            Self::Sell => -1,
        }
    }
}

impl Neg for Side {
    type Output = Self;
    fn neg(self) -> Self {
        self.opposite()
    }
}
