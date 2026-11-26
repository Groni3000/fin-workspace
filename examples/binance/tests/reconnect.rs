//! What the SDK's market-data streams do when the server goes away, against a local fake server.

mod common;

use binance_sdk::config::ConfigurationWebsocketStreams;
use binance_sdk::models::{WebsocketEvent, WebsocketStreamsConnectConfig};
use binance_sdk::spot::SpotWsStreams;
use binance_sdk::spot::websocket_streams::{KlineIntervalEnum, KlineParams, WebsocketStreams};
use common::{A_WHILE, CANDLE, Command, Connection, SOON, STREAM, Server};
use tokio::sync::mpsc::{UnboundedReceiver, unbounded_channel};
use tokio::time::timeout;

/// The SDK's events, without pings and pongs.
#[derive(Debug, PartialEq)]
enum Event {
    Open,
    Message(String),
    Error(String),
    Close(u16),
}

struct Client {
    connection: WebsocketStreams,
    events: UnboundedReceiver<Event>,
}

impl Client {
    /// Connects with `streams` in the URL, the way `connect_with_config` does.
    async fn connect(server: &Server, streams: &[&str]) -> Self {
        let config = ConfigurationWebsocketStreams::builder()
            .ws_url(server.url.clone())
            .reconnect_delay(100)
            .build()
            .unwrap();
        let connection = SpotWsStreams::from_config(config)
            .connect_with_config(WebsocketStreamsConnectConfig {
                streams: streams.iter().map(|s| s.to_string()).collect(),
                mode: None,
            })
            .await
            .unwrap();
        let (events_tx, events) = unbounded_channel();
        // Runs as long as the connection does, whether or not the `Subscription` is kept.
        connection.subscribe_on_ws_events(move |event| {
            let event = match event {
                WebsocketEvent::Open => Event::Open,
                WebsocketEvent::Message(m) => Event::Message(m),
                WebsocketEvent::Error(e) => Event::Error(e),
                WebsocketEvent::Close(code, _) => Event::Close(code),
                WebsocketEvent::Ping | WebsocketEvent::Pong => return,
            };
            let _ = events_tx.send(event);
        });
        Self { connection, events }
    }

    /// Subscribes to 1-second BTCUSDT candles, the way `record` does.
    async fn subscribe(&self) {
        let params = KlineParams::builder("btcusdt".to_string(), KlineIntervalEnum::Interval1s)
            .build()
            .unwrap();
        self.connection.kline(params).await.unwrap();
    }

    async fn next_event(&mut self) -> Event {
        timeout(SOON, self.events.recv())
            .await
            .expect("an event in time")
            .unwrap()
    }

    async fn assert_no_event(&mut self) {
        let next = timeout(A_WHILE, self.events.recv()).await;
        assert!(next.is_err(), "unexpected event {next:?}");
    }
}

/// Connects without streams and subscribes, then checks that a candle gets through.
async fn subscribed(server: &mut Server) -> (Client, Connection) {
    let mut client = Client::connect(server, &[]).await;
    let mut first = server.next_connection().await;
    assert_eq!(first.path, "/stream?streams=");
    client.subscribe().await;
    first.assert_subscribed().await;
    assert_eq!(client.next_event().await, Event::Open);
    let Event::Message(reply) = client.next_event().await else {
        panic!("expected the subscribe reply")
    };
    assert!(reply.starts_with(r#"{"result":null,"id":"#), "{reply}");
    first.send(Command::Send(CANDLE.to_string()));
    assert_eq!(
        client.next_event().await,
        Event::Message(CANDLE.to_string())
    );
    (client, first)
}

const RESET: &str = "WebSocket protocol error: Connection reset without closing handshake";

/// The reconnect asks for the subscribed stream in its URL, so nothing needs resending.
#[tokio::test(flavor = "current_thread")]
async fn a_dropped_connection_comes_back_with_its_subscription() {
    let mut server = Server::start().await;
    let (mut client, first) = subscribed(&mut server).await;

    first.send(Command::Drop);
    assert_eq!(client.next_event().await, Event::Error(RESET.to_string()));
    let mut second = server.next_connection().await;
    assert_eq!(second.path, format!("/stream?streams={STREAM}"));
    assert_eq!(client.next_event().await, Event::Open);
    second.send(Command::Send(CANDLE.to_string()));
    assert_eq!(
        client.next_event().await,
        Event::Message(CANDLE.to_string())
    );
    second.assert_nothing_received().await;
}

/// Only subscriptions are remembered: streams given at connect time are gone after a reconnect.
#[tokio::test(flavor = "current_thread")]
async fn streams_given_at_connect_are_lost_on_reconnect() {
    let mut server = Server::start().await;
    let mut client = Client::connect(&server, &[STREAM]).await;
    let first = server.next_connection().await;
    assert_eq!(first.path, format!("/stream?streams={STREAM}"));
    assert_eq!(client.next_event().await, Event::Open);

    first.send(Command::Drop);
    assert_eq!(client.next_event().await, Event::Error(RESET.to_string()));
    let mut second = server.next_connection().await;
    assert_eq!(second.path, "/stream?streams=");
    assert_eq!(client.next_event().await, Event::Open);
    second.assert_nothing_received().await;
}

#[tokio::test(flavor = "current_thread")]
async fn going_away_reconnects() {
    let mut server = Server::start().await;
    let (mut client, first) = subscribed(&mut server).await;

    first.send(Command::Close(1001));
    assert_eq!(client.next_event().await, Event::Close(1001));
    let second = server.next_connection().await;
    assert_eq!(second.path, format!("/stream?streams={STREAM}"));
    assert_eq!(client.next_event().await, Event::Open);
}

/// After a normal close the SDK gives up and stays disconnected.
#[tokio::test(flavor = "current_thread")]
async fn a_normal_close_does_not_reconnect() {
    let mut server = Server::start().await;
    let (mut client, first) = subscribed(&mut server).await;

    first.send(Command::Close(1000));
    assert_eq!(client.next_event().await, Event::Close(1000));
    let Event::Error(error) = client.next_event().await else {
        panic!("expected an error")
    };
    assert!(
        error.starts_with("[CRITICAL] Connection ")
            && error.ends_with(" permanently failed: NormalClose"),
        "{error}"
    );
    server.assert_no_connection().await;
    client.assert_no_event().await;
}

/// The SDK has no read timeout: a connection that stays open but goes quiet looks healthy.
#[tokio::test(flavor = "current_thread")]
async fn silence_goes_unnoticed() {
    let mut server = Server::start().await;
    let (mut client, _first) = subscribed(&mut server).await;

    server.assert_no_connection().await;
    client.assert_no_event().await;
}
