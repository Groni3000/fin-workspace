use tradeprim::currency::Currency;

use crate::asset::Asset;
use crate::instruments::TradedInstrument;
use crate::mic::Mic;
use std::fmt::Display;

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Stock {
    base: Asset,
    price_quotation: Asset,
    mic: Mic,
    settlement_currency: Currency,
}

impl Stock {
    pub const fn new(
        base: Asset,
        price_quotation: Asset,
        mic: Mic,
        settlement_currency: Currency,
    ) -> Self {
        Self {
            base,
            price_quotation,
            mic,
            settlement_currency,
        }
    }
}

impl TradedInstrument for Stock {
    fn base(&self) -> &Asset {
        &self.base
    }

    fn price_quotation(&self) -> &Asset {
        &self.price_quotation
    }

    fn mic(&self) -> &Mic {
        &self.mic
    }

    fn settlement_currency(&self) -> &Currency {
        &self.settlement_currency
    }
}

impl Display for Stock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Stock:{}/{}@{}({})",
            self.base, self.price_quotation, self.mic, self.settlement_currency
        )
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use crate::_assert_owned;
    use crate::asset::AssetClass;

    use super::*;
    //fixture
    fn aapl() -> Stock {
        Stock::new(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            Currency::usd(),
        )
    }

    #[test]
    fn test_stock_display() {
        let stock = aapl();

        assert_eq!(
            format!("{}", stock),
            "Stock:Equity|AAPL/Currency|USD@XNAS(USD)"
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_stock_serialize() {
        let stock = aapl();
        let serialized = serde_json::to_string(&stock).expect("Stock should be serializable");
        let expected = "{\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\"}";

        assert_eq!(expected, serialized);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_stock_deserialize() {
        let expected = aapl();
        let stock_str = "{\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\"}";
        let deserialized: Stock =
            serde_json::from_str(stock_str).expect("Stock should be deserializable");

        assert_eq!(expected, deserialized);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_stock_is_owned() {
        _assert_owned::<Stock>();
    }
}
