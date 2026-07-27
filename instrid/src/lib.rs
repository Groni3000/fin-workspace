pub mod asset;
pub mod inline_str;
pub mod instruments;
pub mod mic;
pub mod spec;
pub mod tenor;

// TODO:
//  - serde deserializes Cow always using Owned arm...
//    It seems I need to write my visitors to get rid of allocations (for 2/3 cases).

/// Common imports for users of this crate.
///
/// ```
/// use instrid::prelude::*;
/// ```
pub mod prelude {
    pub use crate::asset::{Asset, AssetClass};
    pub use crate::instruments::{
        ExerciseStyle, FuturesContract, Instrument, OptionContract, OptionKind, Stock,
        TradedInstrument,
    };
    pub use crate::mic::{Date, MarketCategoryCode, Mic, MicStatus, MicType, mic_by_code};
    pub use crate::tenor::Tenor;
}

/// Used to check that `T` borrows nothing from
/// a deserializer input.
///
/// i.e. `T` does not hold any `&'de` reference-field.
///
/// **It says nothing about the process of deserialization.
/// It just checks resulting type.**
#[cfg(feature = "serde")]
pub(crate) fn _assert_owned<T: serde::de::DeserializeOwned>() {}
