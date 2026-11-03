#![doc = include_str!("../README.md")]

pub mod record;
pub mod stream;
pub mod tagged;

pub use record::{Candle, Instrumented, RelevantPrice, Symboled, Timestamped};
pub use stream::MarketData;
pub use tagged::Tagged;
