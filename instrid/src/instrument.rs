use crate::{asset::Asset, instruments::stock::Stock, mic::Mic};

/// Represents a trading instrument.
pub enum Instrument {
    Stock(Stock),
}

/// Trait that shows that an `Instrument` is uniquely identified in the most general way.
///
/// It basically means:
///     - We buy `base` asset
///     - Using `quote` asset
///     - On `mic` venue
pub trait BaseInstrument {
    /// Returns a reference to the base asset of this instrument.
    fn base(&self) -> &Asset;
    /// Returns a reference to the quote asset of this instrument.
    fn quote(&self) -> &Asset;
    /// Returns a reference to the MIC of this instrument.
    fn mic(&self) -> &Mic;
}

impl BaseInstrument for Instrument {
    fn base(&self) -> &Asset {
        match self {
            Instrument::Stock(stock) => stock.base(),
        }
    }

    fn quote(&self) -> &Asset {
        match self {
            Instrument::Stock(stock) => stock.quote(),
        }
    }

    fn mic(&self) -> &Mic {
        match self {
            Instrument::Stock(stock) => stock.mic(),
        }
    }
}
