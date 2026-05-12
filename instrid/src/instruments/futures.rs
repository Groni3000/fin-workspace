use std::fmt::Display;

use crate::asset::Asset;
use crate::instruments::TradedInstrument;
use crate::mic::Mic;
use crate::tenor::Tenor;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct FuturesContract {
    base: Asset,
    quote: Asset,
    mic: Mic,
    year: u16,
    tenor: Tenor,
    day: Option<u8>,
}

impl FuturesContract {
    pub const fn new(
        base: Asset,
        quote: Asset,
        mic: Mic,
        year: u16,
        tenor: Tenor,
        day: Option<u8>,
    ) -> Self {
        Self {
            base,
            quote,
            mic,
            year,
            tenor,
            day,
        }
    }

    pub fn with_year(self, year: u16) -> Self {
        Self { year, ..self }
    }

    pub fn with_tenor(self, tenor: Tenor) -> Self {
        Self { tenor, ..self }
    }

    pub fn with_year_tenor(self, year: u16, tenor: Tenor) -> Self {
        Self {
            year,
            tenor,
            ..self
        }
    }

    pub fn tenor(&self) -> Tenor {
        self.tenor
    }
}

impl TradedInstrument for FuturesContract {
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

impl Display for FuturesContract {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Futures:{}/{}@{} {:04}-{:02}",
            self.base,
            self.quote,
            self.mic,
            self.year,
            self.tenor.ordinal()
        )?;

        if let Some(day) = self.day {
            write!(f, "-{:02}", day)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::asset::AssetClass;

    use super::*;

    #[test]
    fn display_without_day() {
        let f = FuturesContract::new(
            Asset::new("CL", AssetClass::Commodity),
            Asset::new("USD", AssetClass::Currency),
            Mic::xnas(),
            2026,
            Tenor::June,
            None,
        );
        assert_eq!(
            f.to_string(),
            "Futures:(Commodity)CL/(Currency)USD@XNAS 2026-06",
        );
    }

    #[test]
    fn display_with_day() {
        let f = FuturesContract::new(
            Asset::new("CL", AssetClass::Commodity),
            Asset::new("USD", AssetClass::Currency),
            Mic::xnas(),
            2026,
            Tenor::June,
            Some(20),
        );
        assert_eq!(
            f.to_string(),
            "Futures:(Commodity)CL/(Currency)USD@XNAS 2026-06-20",
        );
    }
}
