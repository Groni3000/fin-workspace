//! The feed against a local fake server: when it replaces the connection, and when it doesn't.

mod common;

use std::sync::mpsc::{self, TryRecvError};
use std::time::Duration;

use binance_example::feed::{self, FeedEvent, Reason, Watchdog};
use binance_example::gap::Gap;
use binance_sdk::config::ConfigurationWebsocketStreams;
use binance_sdk::spot::SpotWsStreams;
use common::{A_WHILE, CANDLE, Command, SOON, STREAM, Server, candle_at, unreachable_url};
use mdata::HasTimestamp;
use tokio::sync::oneshot;
use tokio::task::JoinHandle;
use tokio::time::{Instant, sleep, timeout};

const QUICK: Watchdog = Watchdog {
    silence: Duration::from_millis(300),
    backoff_min: Duration::from_millis(50),
    backoff_max: Duration::from_millis(200),
};

const fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

/// [`CANDLE`]'s open time.
const CANDLE_OPEN: &str = "2026-11-26T01:46:05Z";

struct Feed {
    events: mpsc::Receiver<FeedEvent>,
    stop: oneshot::Sender<()>,
    task: JoinHandle<()>,
}

impl Feed {
    fn start(url: String, watchdog: Watchdog) -> Self {
        let config = ConfigurationWebsocketStreams::builder()
            .ws_url(url)
            .reconnect_delay(100)
            .build()
            .unwrap();
        let streams = SpotWsStreams::from_config(config);
        let (events_tx, events) = mpsc::channel();
        let (stop, stopped) = oneshot::channel::<()>();
        let task = tokio::spawn(async move {
            let stopped = async {
                let _ = stopped.await;
            };
            feed::run(&streams, "BTCUSDT", watchdog, &events_tx, stopped).await;
        });
        Self { events, stop, task }
    }

    async fn next_event(&mut self) -> FeedEvent {
        let deadline = Instant::now() + SOON;
        loop {
            match self.events.try_recv() {
                Ok(event) => return event,
                Err(TryRecvError::Empty) if Instant::now() < deadline => sleep(ms(5)).await,
                Err(e) => panic!("no event in time: {e:?}"),
            }
        }
    }

    async fn next_candle_open(&mut self) -> String {
        match self.next_event().await {
            FeedEvent::Kline(k) => k.candle.timestamp().to_string(),
            other => panic!("expected a candle, got {other:?}"),
        }
    }

    async fn next_gap(&mut self) -> (String, String) {
        match self.next_event().await {
            FeedEvent::Gap(Gap { from, until }) => (from.to_string(), until.to_string()),
            other => panic!("expected a gap, got {other:?}"),
        }
    }

    async fn next_reconnect(&mut self) -> (Reason, Duration) {
        match self.next_event().await {
            FeedEvent::Reconnecting { reason, after } => (reason, after),
            other => panic!("expected a reconnect, got {other:?}"),
        }
    }

    async fn assert_no_event(&mut self) {
        sleep(A_WHILE).await;
        let next = self.events.try_recv();
        assert!(next.is_err(), "unexpected event {next:?}");
    }

    async fn stop(self) {
        self.stop.send(()).unwrap();
        timeout(SOON, self.task)
            .await
            .expect("stopped in time")
            .unwrap();
    }
}

#[tokio::test(flavor = "current_thread")]
async fn candles_and_invalid_messages_are_passed_on() {
    let mut server = Server::start().await;
    let mut feed = Feed::start(server.url.clone(), QUICK);
    let mut connection = server.next_connection().await;
    assert_eq!(connection.path, "/stream?streams=");
    connection.assert_subscribed().await;

    connection.send(Command::Send(CANDLE.to_string()));
    assert_eq!(feed.next_candle_open().await, CANDLE_OPEN);
    connection.send(Command::Send("nope".to_string()));
    let FeedEvent::Invalid { raw, error } = feed.next_event().await else {
        panic!("expected an invalid message")
    };
    assert_eq!(raw, "nope");
    assert!(error.to_string().starts_with("invalid JSON: "), "{error}");

    feed.stop().await;
    connection.assert_closed().await;
}

/// Each replacement waits twice as long as the one before, until a candle arrives.
#[tokio::test(flavor = "current_thread")]
async fn silence_gets_a_fresh_connection() {
    let mut server = Server::start().await;
    let mut feed = Feed::start(server.url.clone(), QUICK);
    let mut first = server.next_connection().await;
    first.assert_subscribed().await;

    assert_eq!(feed.next_reconnect().await, (Reason::Silence, ms(50)));
    first.assert_closed().await;
    let mut second = server.next_connection().await;
    second.assert_subscribed().await;

    assert_eq!(feed.next_reconnect().await, (Reason::Silence, ms(100)));
    let mut third = server.next_connection().await;
    third.assert_subscribed().await;
    third.send(Command::Send(CANDLE.to_string()));
    assert_eq!(feed.next_candle_open().await, CANDLE_OPEN);

    assert_eq!(feed.next_reconnect().await, (Reason::Silence, ms(50)));
    feed.stop().await;
}

/// Disconnecting a connection the SDK gave up on doesn't hang.
#[tokio::test(flavor = "current_thread")]
async fn a_normal_close_gets_a_fresh_connection() {
    let mut server = Server::start().await;
    let mut feed = Feed::start(server.url.clone(), QUICK);
    let mut first = server.next_connection().await;
    first.assert_subscribed().await;

    first.send(Command::Close(1000));
    let (Reason::GaveUp(error), after) = feed.next_reconnect().await else {
        panic!("expected the SDK to give up")
    };
    assert!(
        error.ends_with("permanently failed: NormalClose"),
        "{error}"
    );
    assert_eq!(after, ms(50));
    let mut second = server.next_connection().await;
    second.assert_subscribed().await;
    feed.stop().await;
}

#[tokio::test(flavor = "current_thread")]
async fn a_refused_subscription_gets_a_fresh_connection() {
    let mut server = Server::start().await;
    let mut feed = Feed::start(server.url.clone(), QUICK);
    let mut first = server.next_connection().await;
    first.assert_subscribed().await;

    let refusal = r#"{"error":{"code":2,"msg":"Invalid request"},"id":"7"}"#;
    first.send(Command::Send(refusal.to_string()));
    assert_eq!(
        feed.next_reconnect().await,
        (
            Reason::Refused(r#"{"code":2,"msg":"Invalid request"}"#.to_string()),
            ms(50)
        )
    );
    server.next_connection().await.assert_subscribed().await;
    feed.stop().await;
}

/// The SDK reconnects with the stream in the URL; the feed sees only the candles.
#[tokio::test(flavor = "current_thread")]
async fn a_dropped_connection_is_left_to_the_sdk() {
    let patient = Watchdog {
        silence: ms(1500),
        ..QUICK
    };
    let mut server = Server::start().await;
    let mut feed = Feed::start(server.url.clone(), patient);
    let mut first = server.next_connection().await;
    first.assert_subscribed().await;
    first.send(Command::Send(CANDLE.to_string()));
    assert_eq!(feed.next_candle_open().await, CANDLE_OPEN);

    first.send(Command::Drop);
    let mut second = server.next_connection().await;
    assert_eq!(second.path, format!("/stream?streams={STREAM}"));
    second.assert_nothing_received().await;
    second.send(Command::Send(candle_at(1)));
    assert_eq!(feed.next_candle_open().await, "2026-11-26T01:46:06Z");
    feed.assert_no_event().await;
    feed.stop().await;
}

#[tokio::test(flavor = "current_thread")]
async fn the_wait_doubles_up_to_the_cap_while_unreachable() {
    let mut feed = Feed::start(unreachable_url().await, QUICK);
    let mut waits = Vec::new();
    for _ in 0..4 {
        let (reason, after) = feed.next_reconnect().await;
        assert!(matches!(reason, Reason::ConnectFailed(_)), "{reason:?}");
        waits.push(after);
    }
    assert_eq!(waits, [ms(50), ms(100), ms(200), ms(200)]);
    feed.stop().await;
}

/// Every candle once, in order; a gap is reported just before the candle after it.
#[tokio::test(flavor = "current_thread")]
async fn gaps_are_reported_and_repeats_dropped() {
    let mut server = Server::start().await;
    let mut feed = Feed::start(server.url.clone(), QUICK);
    let mut connection = server.next_connection().await;
    connection.assert_subscribed().await;

    for s in [0, 1, 3, 1, 4] {
        connection.send(Command::Send(candle_at(s)));
    }
    assert_eq!(feed.next_candle_open().await, "2026-11-26T01:46:05Z");
    assert_eq!(feed.next_candle_open().await, "2026-11-26T01:46:06Z");
    assert_eq!(
        feed.next_gap().await,
        (
            "2026-11-26T01:46:07Z".to_string(),
            "2026-11-26T01:46:08Z".to_string()
        )
    );
    assert_eq!(feed.next_candle_open().await, "2026-11-26T01:46:08Z");
    assert_eq!(feed.next_candle_open().await, "2026-11-26T01:46:09Z");
    feed.stop().await;
}

/// The tracker outlives the connection, so a gap across a replacement is reported too.
#[tokio::test(flavor = "current_thread")]
async fn a_gap_across_a_fresh_connection_is_reported() {
    let mut server = Server::start().await;
    let mut feed = Feed::start(server.url.clone(), QUICK);
    let mut first = server.next_connection().await;
    first.assert_subscribed().await;
    first.send(Command::Send(candle_at(0)));
    assert_eq!(feed.next_candle_open().await, "2026-11-26T01:46:05Z");

    first.send(Command::Close(1000));
    assert!(matches!(
        feed.next_reconnect().await,
        (Reason::GaveUp(_), _)
    ));
    let mut second = server.next_connection().await;
    second.assert_subscribed().await;
    second.send(Command::Send(candle_at(3)));
    assert_eq!(
        feed.next_gap().await,
        (
            "2026-11-26T01:46:06Z".to_string(),
            "2026-11-26T01:46:08Z".to_string()
        )
    );
    assert_eq!(feed.next_candle_open().await, "2026-11-26T01:46:08Z");
    feed.stop().await;
}
