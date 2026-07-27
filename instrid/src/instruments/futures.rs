use std::fmt::Display;

use tradeprim::currency::Currency;

use crate::asset::Asset;
use crate::instruments::TradedInstrument;
use crate::mic::Mic;
use crate::tenor::Tenor;

#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct FuturesContract {
    base: Asset,
    price_quotation: Asset,
    mic: Mic,
    settlement_currency: Currency,
    year: u16,
    tenor: Tenor,
    day: Option<u8>,
}

impl FuturesContract {
    pub const fn new(
        base: Asset,
        price_quotation: Asset,
        mic: Mic,
        settlement_currency: Currency,
        year: u16,
        tenor: Tenor,
        day: Option<u8>,
    ) -> Self {
        Self {
            base,
            price_quotation,
            mic,
            settlement_currency,
            year,
            tenor,
            day,
        }
    }

    pub fn with_year(self, year: u16) -> Self {
        Self {
            year,
            day: None,
            ..self
        }
    }

    pub fn with_tenor(self, tenor: Tenor) -> Self {
        Self {
            tenor,
            day: None,
            ..self
        }
    }

    pub fn with_year_tenor(self, year: u16, tenor: Tenor) -> Self {
        Self {
            year,
            tenor,
            day: None,
            ..self
        }
    }

    pub fn tenor(&self) -> Tenor {
        self.tenor
    }

    pub fn year(&self) -> u16 {
        self.year
    }

    pub fn day(&self) -> Option<u8> {
        self.day
    }

    pub fn base(&self) -> &Asset {
        &self.base
    }

    pub fn price_quotation(&self) -> &Asset {
        &self.price_quotation
    }

    pub fn mic(&self) -> &Mic {
        &self.mic
    }

    pub fn settlement_currency(&self) -> &Currency {
        &self.settlement_currency
    }
}

impl TradedInstrument for FuturesContract {
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

impl Display for FuturesContract {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Futures:{}/{}@{}({}) {:04}-{:02}",
            self.base,
            self.price_quotation,
            self.mic,
            self.settlement_currency,
            self.year,
            self.tenor.ordinal(),
        )?;

        if let Some(day) = self.day {
            write!(f, "-{:02}", day)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use crate::_assert_owned;
    use crate::{asset::AssetClass, mic::MicIso};

    use super::*;

    // fixtures
    fn cl() -> FuturesContract {
        FuturesContract::new(
            Asset::new("CL", AssetClass::Commodity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            MicIso::xnas().into(),
            Currency::usd(),
            2026,
            Tenor::June,
            None,
        )
    }

    fn cl_with_day() -> FuturesContract {
        FuturesContract::new(
            Asset::new("CL", AssetClass::Commodity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            MicIso::xnas().into(),
            Currency::usd(),
            2026,
            Tenor::June,
            Some(20),
        )
    }

    #[test]
    fn display_without_day() {
        let f = cl();
        assert_eq!(
            f.to_string(),
            "Futures:Commodity|CL/Currency|USD@XNAS(USD) 2026-06",
        );
    }

    #[test]
    fn display_with_day() {
        let f = cl_with_day();
        assert_eq!(
            f.to_string(),
            "Futures:Commodity|CL/Currency|USD@XNAS(USD) 2026-06-20",
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_futures_serialize() {
        let f = cl();
        let serialized =
            serde_json::to_string(&f).expect("Futures contract should be serializable");
        let expected = "{\"base\":{\"name\":\"CL\",\"class\":\"Commodity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2026,\"tenor\":6,\"day\":null}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_futures_deserialize() {
        let serialized = "{\"base\":{\"name\":\"CL\",\"class\":\"Commodity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2026,\"tenor\":6,\"day\":null}";
        let expected = cl();
        let deserialized: FuturesContract =
            serde_json::from_str(serialized).expect("Futures contract should be deserializable");

        assert_eq!(deserialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_futures_with_day_serialize() {
        let f = cl_with_day();
        let serialized =
            serde_json::to_string(&f).expect("Futures contract should be serializable");
        let expected = "{\"base\":{\"name\":\"CL\",\"class\":\"Commodity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2026,\"tenor\":6,\"day\":20}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_futures_with_day_deserialize() {
        let serialized = "{\"base\":{\"name\":\"CL\",\"class\":\"Commodity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"year\":2026,\"tenor\":6,\"day\":20,\"settlement_currency\":\"USD\"}";
        let expected = cl_with_day();
        let deserialized: FuturesContract =
            serde_json::from_str(serialized).expect("Futures contract should be deserializable");

        assert_eq!(deserialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_futures_is_owned() {
        _assert_owned::<FuturesContract>();
    }
}
