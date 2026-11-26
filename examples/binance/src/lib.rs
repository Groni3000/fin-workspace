//! Live trading on Binance Spot.

pub mod bridge;
pub mod feed;
pub mod gap;
pub mod instruments;
pub mod kline;
pub mod live;
pub mod orders;
pub mod profile;

use std::time::{SystemTime, UNIX_EPOCH};

use binance_sdk::config::{
    ConfigurationRestApi, ConfigurationWebsocketApi, ConfigurationWebsocketStreams,
};
use binance_sdk::spot::websocket_api::WebsocketApiHandle;
use binance_sdk::spot::websocket_streams::WebsocketStreamsHandle;
use binance_sdk::spot::{SpotRestApi, SpotWsApi, SpotWsStreams, rest_api::RestApi};
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

    /// A WebSocket API client (requests, and the account's own events) for this environment's URL.
    pub fn ws_api(self, config: ConfigurationWebsocketApi) -> WebsocketApiHandle {
        match self {
            Env::Testnet => SpotWsApi::testnet(config),
            Env::Demo => SpotWsApi::demo(config),
            Env::Live => SpotWsApi::production(config),
        }
    }

    /// A market-data streams client for this environment's URL.
    pub fn streams(self, config: ConfigurationWebsocketStreams) -> WebsocketStreamsHandle {
        match self {
            Env::Testnet => SpotWsStreams::testnet(config),
            Env::Demo => SpotWsStreams::demo(config),
            Env::Live => SpotWsStreams::production(config),
        }
    }
}

/// Binance's clock and ours, in ms since the Unix epoch. Ours is taken halfway through the
/// request, so the network delay cancels out of the difference.
pub async fn clocks(
    client: &RestApi,
) -> Result<(i64, i64), Box<dyn std::error::Error + Send + Sync>> {
    let sent = SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis() as i64;
    let server = client
        .time()
        .await?
        .data()
        .await?
        .server_time
        .ok_or("no serverTime")?;
    let received = SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis() as i64;
    Ok((server, (sent + received) / 2))
}
