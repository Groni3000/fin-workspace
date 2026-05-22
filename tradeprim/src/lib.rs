pub mod fill;
use std::{
    fmt::Display,
    ops::{Add, Neg, Sub},
};

use instrid::prelude::*;
use rust_decimal::Decimal;

/// Represents an amount of a particular asset.
///
/// A particular interesting implication of this
/// structure is that you can use it for
/// - base asset - representing quantity
/// - quote asset - representing value/price of base asset
///
/// But... The most important thing about representing
/// a base asset "Amount" is it being `> 0`, so unfortunately
/// it's not recommended to use this for representing base asset.
///
/// So, we will probably wrap this struct into a wrapper with
/// invariants that ensure `> 0` quantity.
///
/// Note: if you care about size => you'd probably want to
/// drop `asset` "label" which will reduce the size from
/// 32 -> 16 bytes.
#[derive(Debug, Clone, Copy)]
pub struct Amount {
    quantity: Decimal,
    asset: Asset,
}

impl Amount {
    pub fn new(quantity: Decimal, asset: Asset) -> Self {
        Self { quantity, asset }
    }

    /// Adds two amounts if they have the same asset, otherwise returns `None`.
    pub fn try_add(self, rhs: Amount) -> Option<Self> {
        if self.asset != rhs.asset {
            return None;
        }
        Some(Self::new(self.quantity + rhs.quantity, self.asset))
    }

    /// Subtracts two amounts if they have the same asset, otherwise returns `None`.
    pub fn try_sub(self, rhs: Amount) -> Option<Self> {
        if self.asset != rhs.asset {
            return None;
        }
        Some(Self::new(self.quantity - rhs.quantity, self.asset))
    }

    /// Multiplies two amounts if they have the same asset, otherwise returns `None`.
    pub fn try_mul(self, rhs: Amount) -> Option<Self> {
        if self.asset != rhs.asset {
            return None;
        }
        Some(Self::new(self.quantity * rhs.quantity, self.asset))
    }

    pub fn quantity(&self) -> Decimal {
        self.quantity
    }

    pub fn asset(&self) -> Asset {
        self.asset
    }
}

impl Display for Amount {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} {}", self.quantity, self.asset.name())
    }
}

impl Add for Amount {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(self.asset, rhs.asset);
        Amount {
            quantity: self.quantity + rhs.quantity,
            asset: self.asset,
        }
    }
}

impl Neg for Amount {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.quantity, self.asset)
    }
}

impl Sub for Amount {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        assert_eq!(self.asset, rhs.asset);
        Self::new(self.quantity - rhs.quantity, self.asset)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Side {
    Buy,
    Sell,
}

impl Side {
    pub fn sign(self) -> Decimal {
        self.into()
    }

    pub fn opposite(self) -> Self {
        match self {
            Self::Buy => Self::Sell,
            Self::Sell => Self::Buy,
        }
    }
}

impl From<Side> for Decimal {
    fn from(s: Side) -> Self {
        match s {
            Side::Buy => Decimal::ONE,
            Side::Sell => Decimal::NEGATIVE_ONE,
        }
    }
}

impl Neg for Side {
    type Output = Self;
    fn neg(self) -> Self {
        self.opposite()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal_macros::dec;

    #[test]
    fn test_amount_display() {
        let asset =
            Asset::new("BTC", AssetClass::Currency).expect("Asset got incorrect parameters");
        let amount = Amount {
            quantity: dec!(1.5),
            asset,
        };
        assert_eq!(format!("{}", amount), "1.5 BTC");
    }

    #[test]
    fn test_neg() {
        let asset =
            Asset::new("BTC", AssetClass::Currency).expect("Asset got incorrect parameters");
        let amount = Amount::new(dec!(1.5), asset);
        let neg_amount = -amount;
        assert_eq!(format!("{}", neg_amount), "-1.5 BTC");
        assert_eq!(neg_amount.quantity, dec!(-1.5));
    }

    #[test]
    fn test_add() {
        let asset =
            Asset::new("BTC", AssetClass::Currency).expect("Asset got incorrect parameters");
        let amount1 = Amount::new(dec!(1.5), asset);
        let amount2 = Amount::new(dec!(2.0), asset);
        let sum = amount1 + amount2;
        assert_eq!(format!("{}", sum), "3.5 BTC");
        assert_eq!(sum.quantity, dec!(3.5));
    }

    #[test]
    fn test_sub() {
        let asset =
            Asset::new("BTC", AssetClass::Currency).expect("Asset got incorrect parameters");
        let amount1 = Amount::new(dec!(3.0), asset);
        let amount2 = Amount::new(dec!(2.5), asset);
        let diff = amount1 - amount2;
        assert_eq!(format!("{}", diff), "0.5 BTC");
        assert_eq!(diff.quantity, dec!(0.5));
    }
}
