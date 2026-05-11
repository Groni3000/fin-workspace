use crate::asset::Asset;
use crate::instrument::BaseInstrument;
use crate::mic::Mic;
use std::fmt::Display;

#[derive(Debug, PartialEq, Eq)]
pub struct Stock {
    base: Asset,
    quote: Asset,
    mic: Mic,
}

impl Stock {
    pub const fn new(base: Asset, quote: Asset, mic: Mic) -> Self {
        Self { base, quote, mic }
    }
}

impl BaseInstrument for Stock {
    fn base(&self) -> &Asset {
        &self.base
    }

    fn quote(&self) -> &Asset {
        &self.quote
    }

    fn mic(&self) -> &Mic {
        &self.mic
    }
}

impl Display for Stock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Stock:{}/{}@{}", self.base, self.quote, self.mic)
    }
}

#[cfg(test)]
mod tests {
    use crate::asset::AssetClass;

    use super::*;

    #[test]
    fn test_stock_display() {
        let stock = Stock::new(
            Asset::new("AAPL", AssetClass::Equity),
            Asset::new("USD", AssetClass::Currency),
            Mic::xnas(),
        );

        assert_eq!(
            format!("{}", stock),
            "Stock:(Equity)AAPL/(Currency)USD@XNAS"
        );
    }
}
