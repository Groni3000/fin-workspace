use std::fmt::Display;

use crate::{
    asset::Asset,
    instruments::{futures::FuturesContract, stock::Stock},
    mic::Mic,
};

/// Represents a trading instrument.
#[derive(Debug, PartialEq, Eq)]
pub enum Instrument {
    Stock(Stock),
    Futures(FuturesContract),
}

/// Trait that shows that an `Instrument` is uniquely identified in the most general way.
///
/// It basically means:
///     - We buy `base` asset
///     - Using `quote` asset
///     - On `mic` venue
pub trait TradedInstrument {
    /// Returns a reference to the base asset of this instrument.
    fn base(&self) -> &Asset;
    /// Returns a reference to the quote asset of this instrument.
    fn quote(&self) -> &Asset;
    /// Returns a reference to the MIC of this instrument.
    fn mic(&self) -> &Mic;
}

impl TradedInstrument for Instrument {
    fn base(&self) -> &Asset {
        match self {
            Instrument::Stock(stock) => stock.base(),
            Instrument::Futures(futures) => futures.base(),
        }
    }

    fn quote(&self) -> &Asset {
        match self {
            Instrument::Stock(stock) => stock.quote(),
            Instrument::Futures(futures) => futures.quote(),
        }
    }

    fn mic(&self) -> &Mic {
        match self {
            Instrument::Stock(stock) => stock.mic(),
            Instrument::Futures(futures) => futures.mic(),
        }
    }
}

impl Display for Instrument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instrument::Stock(s) => s.fmt(f),
            Instrument::Futures(fu) => fu.fmt(f),
        }
    }
}
