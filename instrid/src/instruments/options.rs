use std::fmt::Display;

use rust_decimal::Decimal;

use crate::{asset::Asset, mic::Mic, prelude::TradedInstrument, tenor::Tenor};

#[derive(Debug, PartialEq, Eq)]
pub struct OptionContract {
    base: Asset,
    quote: Asset,
    mic: Mic,
    year: u16,
    tenor: Tenor,
    day: u8,
    kind: OptionKind,
    style: ExerciseStyle,
    strike: Decimal,
}

/// Represents the kind of option contract, either a Put or a Call.
///
/// **Exercise style agnostic.**
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
        year: u16,
        tenor: Tenor,
        day: u8,
        kind: OptionKind,
        style: ExerciseStyle,
        strike: Decimal,
    ) -> Self {
        Self {
            base,
            quote,
            mic,
            year,
            tenor,
            day,
            kind,
            style,
            strike,
        }
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
            self.strike.normalize(),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::asset::AssetClass;
    use rust_decimal_macros::dec;

    use super::*;

    fn aapl_call_200_dec25() -> OptionContract {
        OptionContract::new(
            Asset::new("AAPL", AssetClass::Equity).expect("Asset got incorrect parameters"),
            Asset::new("USD", AssetClass::Currency).expect("Asset got incorrect parameters"),
            Mic::xnas(),
            2025,
            Tenor::December,
            19,
            OptionKind::Call,
            ExerciseStyle::American,
            dec!(200.00),
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
            2025,
            Tenor::December,
            19,
            OptionKind::Put,
            ExerciseStyle::American,
            dec!(200.00),
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
            2025,
            Tenor::December,
            19,
            OptionKind::Call,
            ExerciseStyle::European,
            dec!(200.00),
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
            2025,
            Tenor::December,
            19,
            OptionKind::Call,
            ExerciseStyle::American,
            dec!(210.00),
        );
        assert_ne!(strike_200, strike_210);
    }

    #[test]
    fn strike_display_trims_trailing_zeros() {
        let s = aapl_call_200_dec25().to_string();
        assert!(s.ends_with("#200"), "expected '#200' suffix, got: {s}");
    }
}
