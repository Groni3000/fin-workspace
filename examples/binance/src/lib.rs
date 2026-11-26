//! Live trading on Binance Spot.

use binance_sdk::config::ConfigurationRestApi;
use binance_sdk::spot::{SpotRestApi, rest_api::RestApi};

/// Which Binance url to use.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Env {
    /// Prices and order books independent of the real market.
    Testnet,
    /// Prices and order books close to the real market.
    Demo,
    /// Real money.
    Live,
}

impl std::str::FromStr for Env {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "testnet" => Ok(Env::Testnet),
            "demo" => Ok(Env::Demo),
            "live" => Ok(Env::Live),
            _ => Err(format!("unknown env {s:?}: expected testnet, demo or live")),
        }
    }
}

impl Env {
    pub fn rest(self, config: ConfigurationRestApi) -> RestApi {
        match self {
            Env::Testnet => SpotRestApi::testnet(config),
            Env::Demo => SpotRestApi::demo(config),
            Env::Live => SpotRestApi::production(config),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn env_from_str() {
        assert_eq!("testnet".parse(), Ok(Env::Testnet));
        assert_eq!("demo".parse(), Ok(Env::Demo));
        assert_eq!("live".parse(), Ok(Env::Live));
        assert_eq!(
            "prod".parse::<Env>(),
            Err("unknown env \"prod\": expected testnet, demo or live".to_string())
        );
    }
}
