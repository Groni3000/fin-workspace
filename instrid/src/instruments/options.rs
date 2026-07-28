use std::fmt::Display;
use tradeprim::{currency::Currency, prelude::Price};

use crate::instruments::InvalidContractDate;
use crate::{asset::Asset, days_in_month, mic::Mic, prelude::TradedInstrument, tenor::Tenor};

#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
// `remote = "Self"` means that serde will generate ser/de functions for this type
// but not the traits implementations, so we will manually implement traits,
// we can use `new` to verify invariants
#[cfg_attr(feature = "serde", serde(remote = "Self"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OptionContract {
    base: Asset,
    price_quotation: Asset,
    mic: Mic,
    settlement_currency: Currency,
    year: u16,
    tenor: Tenor,
    day: u8,
    kind: OptionKind,
    style: ExerciseStyle,
    strike: Price,
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for OptionContract {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        // Use generated deserialization function.
        let raw = OptionContract::deserialize(deserializer)?;

        // Verify invariants via `new`.
        Self::new(
            raw.base,
            raw.price_quotation,
            raw.mic,
            raw.settlement_currency,
            raw.year,
            raw.tenor,
            raw.day,
            raw.kind,
            raw.style,
            raw.strike,
        )
        .map_err(serde::de::Error::custom)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for OptionContract {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        // Use generated serialization.
        OptionContract::serialize(self, serializer)
    }
}

/// Represents the kind of option contract, either a Put or a Call.
///
/// **Exercise style agnostic.**
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OptionKind {
    /// Put = right to **sell** the underlying at the strike,
    /// the **exercise style** (European/American/Bermudan)
    /// determines when this right can be exercised.
    Put,
    ///Call = right to **buy** the underlying at the strike,
    /// the **exercise style** (European/American/Bermudan)
    /// determines when this right can be exercised.
    Call,
}

impl Display for OptionKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                OptionKind::Put => "Put",
                OptionKind::Call => "Call",
            }
        )
    }
}

/// Represents the exercise style of an option contract,
/// determining when the right can be exercised.
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExerciseStyle {
    /// European = the right can be exercised only at the expiration date.
    European,
    /// American = the right can be exercised at any time before the expiration date.
    American,
    /// Bermudan = the right can be exercised at specific dates before the expiration date.
    Bermudan,
}

impl Display for ExerciseStyle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ExerciseStyle::European => "European",
                ExerciseStyle::American => "American",
                ExerciseStyle::Bermudan => "Bermudan",
            }
        )
    }
}

impl OptionContract {
    /// Create a new options contract, validating that `(year, tenor, day)` is a
    /// real calendar date.
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        base: Asset,
        price_quotation: Asset,
        mic: Mic,
        settlement_currency: Currency,
        year: u16,
        tenor: Tenor,
        day: u8,
        kind: OptionKind,
        style: ExerciseStyle,
        strike: Price,
    ) -> Result<Self, InvalidContractDate> {
        if day == 0 || day > days_in_month(year, tenor.ordinal()) {
            return Err(InvalidContractDate {
                year,
                tenor,
                day: Some(day),
            });
        }

        Ok(Self {
            base,
            price_quotation,
            mic,
            settlement_currency,
            year,
            tenor,
            day,
            kind,
            style,
            strike,
        })
    }
    /// Date validation is on user.
    #[allow(clippy::too_many_arguments)]
    pub const fn new_unchecked(
        base: Asset,
        price_quotation: Asset,
        mic: Mic,
        settlement_currency: Currency,
        year: u16,
        tenor: Tenor,
        day: u8,
        kind: OptionKind,
        style: ExerciseStyle,
        strike: Price,
    ) -> Self {
        Self {
            base,
            price_quotation,
            mic,
            settlement_currency,
            year,
            tenor,
            day,
            kind,
            style,
            strike,
        }
    }

    pub fn settlement_currency(&self) -> &Currency {
        &self.settlement_currency
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

    pub fn year(&self) -> u16 {
        self.year
    }

    pub fn tenor(&self) -> Tenor {
        self.tenor
    }

    pub fn day(&self) -> u8 {
        self.day
    }

    pub fn kind(&self) -> OptionKind {
        self.kind
    }

    pub fn style(&self) -> ExerciseStyle {
        self.style
    }

    pub fn strike(&self) -> Price {
        self.strike
    }
}

impl TradedInstrument for OptionContract {
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

impl Display for OptionContract {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Option:{}/{}@{} {:04}-{:02}-{:02} {}::{}#{}",
            self.base,
            self.price_quotation,
            self.mic,
            self.year,
            self.tenor.ordinal(),
            self.day,
            self.style,
            self.kind,
            self.strike,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    #[cfg(feature = "serde")]
    use crate::_assert_owned;
    use crate::asset::AssetClass;

    use super::*;

    fn aapl_call_200_dec25() -> OptionContract {
        OptionContract::new_unchecked(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            Currency::usd(),
            2025,
            Tenor::December,
            19,
            OptionKind::Call,
            ExerciseStyle::American,
            Price::from_str("200.00").unwrap(),
        )
    }

    #[test]
    fn display_full() {
        assert_eq!(
            aapl_call_200_dec25().to_string(),
            "Option:Equity|AAPL/Currency|USD@XNAS 2025-12-19 American::Call#200",
        );
    }

    #[test]
    fn call_and_put_differ() {
        let call = aapl_call_200_dec25();
        let put = OptionContract::new_unchecked(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            Currency::usd(),
            2025,
            Tenor::December,
            19,
            OptionKind::Put,
            ExerciseStyle::American,
            Price::from_str("200.00").unwrap(),
        );
        assert_ne!(call, put);
    }

    #[test]
    fn style_distinguishes_contracts() {
        let american = aapl_call_200_dec25();
        let european = OptionContract::new_unchecked(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            Currency::usd(),
            2025,
            Tenor::December,
            19,
            OptionKind::Call,
            ExerciseStyle::European,
            Price::from_str("200.00").unwrap(),
        );
        assert_ne!(american, european);
    }

    #[test]
    fn different_strikes_differ() {
        let strike_200 = aapl_call_200_dec25();
        let strike_210 = OptionContract::new_unchecked(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            Currency::usd(),
            2025,
            Tenor::December,
            19,
            OptionKind::Call,
            ExerciseStyle::American,
            Price::from_str("210.00").unwrap(),
        );
        assert_ne!(strike_200, strike_210);
    }

    #[test]
    fn strike_display_trims_trailing_zeros() {
        let s = aapl_call_200_dec25().to_string();
        assert!(s.ends_with("#200"), "expected '#200' suffix, got: {s}");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_option_serialize() {
        let opt = aapl_call_200_dec25();
        let serialized = serde_json::to_string(&opt).unwrap();
        let expected = "{\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2025,\"tenor\":12,\"day\":19,\"kind\":\"Call\",\"style\":\"American\",\"strike\":\"200\"}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_option_deserialize() {
        let serialized = "{\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"price_quotation\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2025,\"tenor\":12,\"day\":19,\"kind\":\"Call\",\"style\":\"American\",\"strike\":\"200\"}";
        let expected = aapl_call_200_dec25();
        let deserialized: OptionContract = serde_json::from_str(serialized).unwrap();

        assert_eq!(deserialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_option_kind_serialize() {
        assert_eq!(
            serde_json::to_string(&OptionKind::Call).unwrap(),
            "\"Call\""
        );
        assert_eq!(serde_json::to_string(&OptionKind::Put).unwrap(), "\"Put\"");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_exercise_style_serialize() {
        assert_eq!(
            serde_json::to_string(&ExerciseStyle::European).unwrap(),
            "\"European\""
        );
        assert_eq!(
            serde_json::to_string(&ExerciseStyle::American).unwrap(),
            "\"American\""
        );
        assert_eq!(
            serde_json::to_string(&ExerciseStyle::Bermudan).unwrap(),
            "\"Bermudan\""
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_option_is_owned() {
        _assert_owned::<OptionContract>();
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_option_kind_is_owned() {
        _assert_owned::<OptionKind>();
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_exercise_style_is_owned() {
        _assert_owned::<ExerciseStyle>();
    }
}
