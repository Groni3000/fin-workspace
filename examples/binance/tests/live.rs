//! The live queue over the real feed and a local fake server.

mod common;

use std::time::Duration;

use binance_example::feed::Watchdog;
use binance_example::live::LiveQueue;
use binance_sdk::config::ConfigurationWebsocketStreams;
use binance_sdk::spot::SpotWsStreams;
use binance_sdk::spot::websocket_streams::WebsocketStreamsHandle;
use common::{Command, Server, candle_at, trade_at, unreachable_url};
use engine::event::{EventSource, Kind};
use mdata::{HasTimestamp, HasVolume};
use tokio::runtime::Runtime;

/// Gives up within seconds, so a queue that never hands anything out fails instead of hanging.
const WATCHDOG: Watchdog = Watchdog {
    silence: Duration::from_secs(1),
    backoff_min: Duration::from_millis(50),
    backoff_max: Duration::from_millis(200),
    give_up: Duration::from_secs(3),
};

/// 2026-11-26T01:46:05Z, [`candle_at`]'s zero, in ns.
const T0: i64 = 1_795_657_565_000_000_000;
const SEC: i64 = 1_000_000_000;

fn streams(url: String) -> WebsocketStreamsHandle {
    let config = ConfigurationWebsocketStreams::builder()
        .ws_url(url)
        .reconnect_delay(100)
        .build()
        .unwrap();
    SpotWsStreams::from_config(config)
}

/// Empty candles are skipped, a gap is only logged, and every event carries the candle's own
/// time; an invalid message comes out at the time of the last candle.
#[test]
fn candles_come_out_at_their_own_time() {
    let server_runtime = Runtime::new().unwrap();
    let mut server = server_runtime.block_on(Server::start());
    let mut queue =
        LiveQueue::start(streams(server.url.clone()), "BTCUSDT".to_string(), WATCHDOG).unwrap();
    let mut connection = server_runtime.block_on(server.next_connection());
    server_runtime.block_on(connection.assert_subscribed());

    for message in [
        candle_at(0),
        trade_at(1),
        candle_at(2),
        trade_at(3),
        trade_at(5),
        "nope".to_string(),
    ] {
        connection.send(Command::Send(message));
    }
    let mut candle = |at: i64| {
        let event = queue.next_event().expect("an event");
        assert_eq!(event.ts(), at);
        let Kind::MarketData(candle) = event.kind() else {
            panic!("expected a candle, got {event:?}")
        };
        assert_eq!(candle.timestamp().as_nanosecond(), i128::from(at));
        assert_eq!(candle.volume().to_string(), "0.5");
    };
    candle(T0 + SEC);
    candle(T0 + 3 * SEC);
    candle(T0 + 5 * SEC);

    let event = queue.next_event().expect("an event");
    assert_eq!(event.ts(), T0 + 5 * SEC);
    let Kind::FeedError(error) = event.kind() else {
        panic!("expected a feed error, got {event:?}")
    };
    assert!(
        error
            .to_string()
            .starts_with(r#"invalid message "nope": invalid JSON: "#),
        "{error}"
    );
}

#[test]
#[should_panic(expected = "market data lost: no candle for ")]
fn losing_the_feed_panics() {
    let url = Runtime::new().unwrap().block_on(unreachable_url());
    let mut queue = LiveQueue::start(streams(url), "BTCUSDT".to_string(), WATCHDOG).unwrap();
    queue.next_event();
}
