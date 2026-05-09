use crate::{asset::Asset, mic::Mic};

/// Represents a trading instrument consisting of a base asset, quote asset, and MIC.
pub enum Instrument {
    Stock,
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
