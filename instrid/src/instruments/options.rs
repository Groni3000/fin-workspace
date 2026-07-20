use std::fmt::Display;
use tradeprim::{currency::Currency, prelude::Price};

use crate::{asset::Asset, mic::Mic, prelude::TradedInstrument, tenor::Tenor};

#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
pub struct OptionContract {
    base: Asset,
    quote: Asset,
    mic: Mic,
    settlement_currency: Currency,
    year: u16,
    tenor: Tenor,
    day: u8,
    kind: OptionKind,
    style: ExerciseStyle,
    strike: Price,
}

/// Represents the kind of option contract, either a Put or a Call.
///
/// **Exercise style agnostic.**
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
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
    pub const fn new(
        base: Asset,
        quote: Asset,
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
            quote,
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
}

impl TradedInstrument for OptionContract {
    fn base(&self) -> &Asset {
        &self.base
    }

    fn quote(&self) -> &Asset {
        &self.quote
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
            self.quote,
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
        OptionContract::new(
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
            "Option:(Equity)AAPL/(Currency)USD@XNAS 2025-12-19 American::Call#200",
        );
    }

    #[test]
    fn call_and_put_differ() {
        let call = aapl_call_200_dec25();
        let put = OptionContract::new(
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
        let european = OptionContract::new(
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
        let strike_210 = OptionContract::new(
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
        let expected = "{\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"quote\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2025,\"tenor\":12,\"day\":19,\"kind\":\"Call\",\"style\":\"American\",\"strike\":\"200\"}";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_option_deserialize() {
        let serialized = "{\"base\":{\"name\":\"AAPL\",\"class\":\"Equity\"},\"quote\":{\"name\":\"USD\",\"class\":\"Currency\"},\"mic\":\"XNAS\",\"settlement_currency\":\"USD\",\"year\":2025,\"tenor\":12,\"day\":19,\"kind\":\"Call\",\"style\":\"American\",\"strike\":\"200\"}";
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
