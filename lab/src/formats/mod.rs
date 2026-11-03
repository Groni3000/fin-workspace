#[cfg(feature = "kafka")]
pub mod custom;
pub mod frd;
#[cfg(feature = "kafka")]
pub mod merged_custom_kafka;
#[cfg(feature = "kafka")]
use serde::{Deserialize, Deserializer};
#[cfg(feature = "kafka")]
use tradeprim::price::Price;

#[cfg(feature = "kafka")]
pub fn de_price_f64<'de, D: Deserializer<'de>>(d: D) -> Result<Price, D::Error> {
    let v = f64::deserialize(d)?;
    Price::try_from(v).map_err(serde::de::Error::custom)
}
