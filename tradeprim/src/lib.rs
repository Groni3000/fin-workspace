use std::fmt::Display;

use instrid::prelude::*;
use rust_decimal::Decimal;

#[derive(Debug)]
pub struct Amount<'a> {
    quantity: Decimal,
    asset: &'a Asset,
}

impl Display for Amount<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.quantity, self.asset.name())
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
            asset: &asset,
        };
        assert_eq!(format!("{}", amount), "1.5 BTC");
    }
}
