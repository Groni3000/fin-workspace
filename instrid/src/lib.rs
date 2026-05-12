pub mod asset;
pub mod instruments;
pub mod mic;
pub mod tenor;

/// Common imports for users of this crate.
///
/// ```
/// use instrid::prelude::*;
/// ```
pub mod prelude {
    pub use crate::asset::{Asset, AssetClass};
    pub use crate::instruments::{FuturesContract, Instrument, Stock, TradedInstrument};
    pub use crate::mic::{Date, MarketCategoryCode, Mic, MicStatus, MicType, mic_by_code};
    pub use crate::tenor::Tenor;
}
