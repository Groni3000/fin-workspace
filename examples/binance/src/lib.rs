//! Live trading on Binance Spot.

pub mod profile;

use binance_sdk::config::ConfigurationRestApi;
use binance_sdk::spot::{SpotRestApi, rest_api::RestApi};
use serde::Deserialize;

/// Which Binance deployment to talk to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Env {
    /// Prices and order books independent of the real market.
    Testnet,
    /// Prices and order books close to the real market.
    Demo,
    /// Real money.
    Live,
}

impl Env {
    /// A REST client for this environment's URL.
    pub fn rest(self, config: ConfigurationRestApi) -> RestApi {
        match self {
            Env::Testnet => SpotRestApi::testnet(config),
            Env::Demo => SpotRestApi::demo(config),
            Env::Live => SpotRestApi::production(config),
        }
    }
}
