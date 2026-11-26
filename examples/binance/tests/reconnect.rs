//! What the SDK's market-data streams do when the server goes away, against a local fake server.

use std::time::Duration;

use binance_sdk::config::ConfigurationWebsocketStreams;
use binance_sdk::models::{WebsocketEvent, WebsocketStreamsConnectConfig};
use binance_sdk::spot::SpotWsStreams;
use binance_sdk::spot::websocket_streams::{KlineIntervalEnum, KlineParams, WebsocketStreams};
use futures_util::{SinkExt, StreamExt};
use tokio::net::TcpListener;
use tokio::sync::mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel};
use tokio::time::timeout;
use tokio_tungstenite::tungstenite::Message;
use tokio_tungstenite::tungstenite::handshake::server::{Request, Response};
use tokio_tungstenite::tungstenite::protocol::CloseFrame;

const STREAM: &str = "btcusdt@kline_1s";

const CANDLE: &str = r#"{"stream":"btcusdt@kline_1s","data":{"e":"kline","E":1795657567024,"s":"BTCUSDT","k":{"t":1795657565000,"T":1795657565999,"s":"BTCUSDT","i":"1s","f":-1,"L":-1,"o":"60760.01000000","c":"60760.01000000","h":"60760.01000000","l":"60760.01000000","v":"0.00000000","n":0,"x":true,"q":"0.00000000","V":"0.00000000","Q":"0.00000000","B":"0"}}}"#;

/// Long enough for anything that happens on localhost.
const SOON: Duration = Duration::from_secs(2);
/// How long to wait before concluding that something doesn't happen.
const A_WHILE: Duration = Duration::from_millis(700);

/// Accepts connections and replies to `SUBSCRIBE` like Binance does.
struct Server {
    url: String,
    connections: UnboundedReceiver<Connection>,
}

/// The server's side of one connection.
struct Connection {
    /// The requested path with its query.
    path: String,
    commands: UnboundedSender<Command>,
    /// Text frames from the client.
    received: UnboundedReceiver<String>,
}

enum Command {
    Send(String),
    Close(u16),
    /// Closes the TCP connection without a close frame.
    Drop,
}

impl Server {
    // The handshake callback's error type is tungstenite's, an HTTP response.
    #[allow(clippy::result_large_err)]
    async fn start() -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let url = format!("ws://{}", listener.local_addr().unwrap());
        let (connections_tx, connections) = unbounded_channel();
        tokio::spawn(async move {
            loop {
                let (tcp, _) = listener.accept().await.unwrap();
                let mut path = String::new();
                let ws =
                    tokio_tungstenite::accept_hdr_async(tcp, |req: &Request, resp: Response| {
                        path = req.uri().to_string();
                        Ok(resp)
                    })
                    .await
                    .unwrap();
                let (commands, mut commands_rx) = unbounded_channel();
                let (received_tx, received) = unbounded_channel();
                let _ = connections_tx.send(Connection {
                    path,
                    commands,
                    received,
                });
                tokio::spawn(async move {
                    let (mut sink, mut stream) = ws.split();
                    loop {
                        tokio::select! {
                            command = commands_rx.recv() => match command {
                                Some(Command::Send(text)) => sink.send(Message::text(text)).await.unwrap(),
                                Some(Command::Close(code)) => {
                                    let frame = CloseFrame { code: code.into(), reason: "".into() };
                                    let _ = sink.send(Message::Close(Some(frame))).await;
                                }
                                Some(Command::Drop) | None => return,
                            },
                            message = stream.next() => match message {
                                Some(Ok(Message::Text(text))) => {
                                    let text = text.to_string();
                                    if let Some(reply) = subscribe_reply(&text) {
                                        sink.send(Message::text(reply)).await.unwrap();
                                    }
                                    let _ = received_tx.send(text);
                                }
                                Some(Ok(_)) => {}
                                Some(Err(_)) | None => return,
                            },
                        }
                    }
                });
            }
        });
        Self { url, connections }
    }

    async fn next_connection(&mut self) -> Connection {
        timeout(SOON, self.connections.recv())
            .await
            .expect("a connection in time")
            .unwrap()
    }

    async fn assert_no_connection(&mut self) {
        assert!(
            timeout(A_WHILE, self.connections.recv()).await.is_err(),
            "unexpected connection"
        );
    }
}

fn subscribe_reply(text: &str) -> Option<String> {
    let request: serde_json::Value = serde_json::from_str(text).ok()?;
    (request["method"] == "SUBSCRIBE")
        .then(|| format!(r#"{{"result":null,"id":{}}}"#, request["id"]))
}

impl Connection {
    fn send(&self, command: Command) {
        self.commands.send(command).unwrap();
    }

    async fn next_received(&mut self) -> String {
        timeout(SOON, self.received.recv())
            .await
            .expect("a frame in time")
            .unwrap()
    }

    async fn assert_nothing_received(&mut self) {
        assert!(
            timeout(A_WHILE, self.received.recv()).await.is_err(),
            "unexpected frame"
        );
    }
}

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
        // The subscription ends when it's dropped, so it's leaked: it lives as long as the test.
        std::mem::forget(connection.subscribe_on_ws_events(move |event| {
            let event = match event {
                WebsocketEvent::Open => Event::Open,
                WebsocketEvent::Message(m) => Event::Message(m),
                WebsocketEvent::Error(e) => Event::Error(e),
                WebsocketEvent::Close(code, _) => Event::Close(code),
                WebsocketEvent::Ping | WebsocketEvent::Pong => return,
            };
            let _ = events_tx.send(event);
        }));
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
    let request: serde_json::Value = serde_json::from_str(&first.next_received().await).unwrap();
    assert_eq!(request["method"], "SUBSCRIBE");
    assert_eq!(request["params"], serde_json::json!([STREAM]));
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
