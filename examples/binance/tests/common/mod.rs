//! A fake Binance stream server on localhost.

// Each test file uses part of it.
#![allow(dead_code)]

use std::time::Duration;

use futures_util::{SinkExt, StreamExt};
use tokio::net::TcpListener;
use tokio::sync::mpsc::{UnboundedReceiver, UnboundedSender, unbounded_channel};
use tokio::time::timeout;
use tokio_tungstenite::tungstenite::Message;
use tokio_tungstenite::tungstenite::handshake::server::{Request, Response};
use tokio_tungstenite::tungstenite::protocol::CloseFrame;

pub const STREAM: &str = "btcusdt@kline_1s";

pub const CANDLE: &str = r#"{"stream":"btcusdt@kline_1s","data":{"e":"kline","E":1795657567024,"s":"BTCUSDT","k":{"t":1795657565000,"T":1795657565999,"s":"BTCUSDT","i":"1s","f":-1,"L":-1,"o":"60760.01000000","c":"60760.01000000","h":"60760.01000000","l":"60760.01000000","v":"0.00000000","n":0,"x":true,"q":"0.00000000","V":"0.00000000","Q":"0.00000000","B":"0"}}}"#;

/// [`CANDLE`], opening `s` seconds later.
pub fn candle_at(s: i64) -> String {
    let open = 1_795_657_565_000 + s * 1000;
    CANDLE.replace(
        r#""t":1795657565000,"T":1795657565999"#,
        &format!(r#""t":{open},"T":{}"#, open + 999),
    )
}

/// Long enough for anything that happens on localhost.
pub const SOON: Duration = Duration::from_secs(2);
/// How long to wait before concluding that something doesn't happen.
pub const A_WHILE: Duration = Duration::from_millis(700);

/// Accepts connections and replies to `SUBSCRIBE` like Binance does.
pub struct Server {
    pub url: String,
    connections: UnboundedReceiver<Connection>,
}

/// The server's side of one connection.
pub struct Connection {
    /// The requested path with its query.
    pub path: String,
    commands: UnboundedSender<Command>,
    /// Text frames from the client.
    received: UnboundedReceiver<String>,
}

pub enum Command {
    Send(String),
    Close(u16),
    /// Closes the TCP connection without a close frame.
    Drop,
}

impl Server {
    // The handshake callback's error type is tungstenite's, an HTTP response.
    #[allow(clippy::result_large_err)]
    pub async fn start() -> Self {
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
                                Some(Command::Send(text)) => { let _ = sink.send(Message::text(text)).await; }
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
                                        let _ = sink.send(Message::text(reply)).await;
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

    pub async fn next_connection(&mut self) -> Connection {
        timeout(SOON, self.connections.recv())
            .await
            .expect("a connection in time")
            .unwrap()
    }

    pub async fn assert_no_connection(&mut self) {
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
    pub fn send(&self, command: Command) {
        self.commands.send(command).unwrap();
    }

    pub async fn next_received(&mut self) -> String {
        timeout(SOON, self.received.recv())
            .await
            .expect("a frame in time")
            .unwrap()
    }

    pub async fn assert_nothing_received(&mut self) {
        assert!(
            timeout(A_WHILE, self.received.recv()).await.is_err(),
            "unexpected frame"
        );
    }
    /// The client's `SUBSCRIBE` for [`STREAM`].
    pub async fn assert_subscribed(&mut self) {
        let request: serde_json::Value = serde_json::from_str(&self.next_received().await).unwrap();
        assert_eq!(request["method"], "SUBSCRIBE");
        assert_eq!(request["params"], serde_json::json!([STREAM]));
    }

    /// The client has closed the connection.
    pub async fn assert_closed(&mut self) {
        let next = timeout(SOON, self.received.recv())
            .await
            .expect("closed in time");
        assert_eq!(next, None);
    }
}

/// A URL nobody listens on.
pub async fn unreachable_url() -> String {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    format!("ws://{}", listener.local_addr().unwrap())
}
