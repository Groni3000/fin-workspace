pub mod price;
use std::ops::Neg;

pub mod prelude {
    pub use crate::Side;
    pub use crate::price::Price;
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
}

impl Neg for Side {
    type Output = Self;
    fn neg(self) -> Self {
        self.opposite()
    }
}
