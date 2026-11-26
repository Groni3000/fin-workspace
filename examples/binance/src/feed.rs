//! A live candle feed that stays connected.
//!
//! The SDK reconnects by itself after a dropped connection or a "going away" close, and asks for
//! the subscribed streams again. It does nothing about two cases, which [`run`] handles by
//! replacing the connection:
//!
//! - silence: there's no read timeout, so a connection that dies quietly looks healthy. 1-second
//!   candles arrive every second, empty seconds included, so a long enough silence means trouble;
//! - giving up: after a normal close (and other codes it considers permanent) the SDK stays
//!   disconnected for good.
//!
//! Candles are followed across connections by a [`GapTracker`]: a gap is reported before the
//! candle after it, and repeated candles are dropped.

use std::fmt::{self, Display};
use std::future::Future;
use std::pin::pin;
use std::sync::mpsc::Sender;
use std::time::Duration;

use binance_sdk::config::ConfigurationWebsocketStreams;
use binance_sdk::models::{ConfigBuildError, WebsocketEvent};
use binance_sdk::spot::websocket_streams::{
    KlineIntervalEnum, KlineParams, WebsocketStreams, WebsocketStreamsHandle,
};
use jiff::SignedDuration;
use mdata::HasTimestamp;
use tokio::sync::mpsc::{UnboundedReceiver, unbounded_channel};
use tokio::time::{Instant, sleep, sleep_until, timeout};

use crate::Env;
use crate::gap::{Gap, GapTracker, Seen};
use crate::kline::{self, Kline, Message, ParseError};

/// How long the SDK waits before reconnecting by itself. Each second waited is a candle to
/// backfill.
const SDK_RECONNECT_DELAY_MS: u64 = 1000;

/// How long a disconnect may take before the connection is dropped instead.
const DISCONNECT_TIMEOUT: Duration = Duration::from_secs(5);

/// The SDK's error once it has stopped reconnecting.
const GAVE_UP: &str = "permanently failed";

/// When to replace a connection, and how long to wait between attempts.
#[derive(Debug, Clone, Copy)]
pub struct Watchdog {
    /// No candle for this long: the connection is replaced. Longer than the SDK's own reconnect
    /// (about 1.5 s) plus testnet's late candles (up to about 1.2 s).
    pub silence: Duration,
    /// The wait before the first new connection. It doubles with each failure in a row and is
    /// back to this after a candle.
    pub backoff_min: Duration,
    pub backoff_max: Duration,
}

impl Default for Watchdog {
    fn default() -> Self {
        Self {
            silence: Duration::from_secs(5),
            backoff_min: Duration::from_secs(1),
            backoff_max: Duration::from_secs(30),
        }
    }
}

#[derive(Debug)]
pub enum FeedEvent {
    Kline(Kline),
    /// Candles missing before the next [`FeedEvent::Kline`].
    Gap(Gap),
    /// A message that didn't parse. The feed carries on.
    Invalid {
        raw: String,
        error: ParseError,
    },
    /// The connection is being replaced; the next one is made `after` this long.
    Reconnecting {
        reason: Reason,
        after: Duration,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reason {
    /// No candle for [`Watchdog::silence`].
    Silence,
    /// The SDK stopped reconnecting; its error.
    GaveUp(String),
    /// Binance refused the subscription; its error.
    Refused(String),
    ConnectFailed(String),
}

impl Display for Reason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Reason::Silence => write!(f, "no candle in time"),
            Reason::GaveUp(e) => write!(f, "the SDK gave up: {e}"),
            Reason::Refused(e) => write!(f, "subscription refused: {e}"),
            Reason::ConnectFailed(e) => write!(f, "cannot connect: {e}"),
        }
    }
}

/// A streams client for `env`, with the SDK's reconnect delay this feed expects.
pub fn streams(env: Env) -> Result<WebsocketStreamsHandle, ConfigBuildError> {
    let config = ConfigurationWebsocketStreams::builder()
        .reconnect_delay(SDK_RECONNECT_DELAY_MS)
        .build()?;
    Ok(env.streams(config))
}

/// Sends the 1-second candles of `symbol` (as Binance spells it, e.g. `BTCUSDT`) until `stop`
/// completes or `events` is closed, replacing the connection when [`Watchdog`] says so.
pub async fn run(
    streams: &WebsocketStreamsHandle,
    symbol: &str,
    watchdog: Watchdog,
    events: &Sender<FeedEvent>,
    stop: impl Future<Output = ()>,
) {
    let mut stop = pin!(stop);
    let mut backoff = watchdog.backoff_min;
    let mut tracker = GapTracker::new(SignedDuration::from_secs(1));
    loop {
        let connected = tokio::select! {
            connected = connect(streams, symbol) => connected,
            () = &mut stop => return,
        };
        let reason = match connected {
            Err(e) => Reason::ConnectFailed(e),
            Ok((connection, mut sdk_events)) => {
                let mut candle_seen = false;
                let ended = tokio::select! {
                    ended = watch(&mut sdk_events, watchdog.silence, events, &mut tracker, &mut candle_seen) => ended,
                    () = &mut stop => None,
                };
                if candle_seen {
                    backoff = watchdog.backoff_min;
                }
                // Bounded, as a dead network may never answer; dropping the connection closes
                // it too.
                let _ = timeout(DISCONNECT_TIMEOUT, connection.disconnect()).await;
                match ended {
                    Some(reason) => reason,
                    None => return,
                }
            }
        };
        let after = backoff;
        backoff = (backoff * 2).min(watchdog.backoff_max);
        if events
            .send(FeedEvent::Reconnecting { reason, after })
            .is_err()
        {
            return;
        }
        tokio::select! {
            () = sleep(after) => {}
            () = &mut stop => return,
        }
    }
}

async fn connect(
    streams: &WebsocketStreamsHandle,
    symbol: &str,
) -> Result<(WebsocketStreams, UnboundedReceiver<WebsocketEvent>), String> {
    let connection = streams.connect().await.map_err(|e| e.to_string())?;
    let (tx, rx) = unbounded_channel();
    // Runs as long as the connection does, whether or not the `Subscription` is kept.
    connection.subscribe_on_ws_events(move |event| {
        let _ = tx.send(event);
    });
    // Subscribing after connecting, not in the connect URL: only subscriptions survive the
    // SDK's reconnects.
    let params = KlineParams::builder(symbol.to_lowercase(), KlineIntervalEnum::Interval1s)
        .build()
        .map_err(|e| e.to_string())?;
    connection.kline(params).await.map_err(|e| e.to_string())?;
    Ok((connection, rx))
}

/// Passes candles on until the connection has to be replaced, and says why. `None`: `events`
/// is closed.
async fn watch(
    sdk_events: &mut UnboundedReceiver<WebsocketEvent>,
    silence: Duration,
    events: &Sender<FeedEvent>,
    tracker: &mut GapTracker,
    candle_seen: &mut bool,
) -> Option<Reason> {
    let mut deadline = Instant::now() + silence;
    loop {
        let event = tokio::select! {
            Some(event) = sdk_events.recv() => event,
            () = sleep_until(deadline) => return Some(Reason::Silence),
        };
        let out = match event {
            WebsocketEvent::Message(raw) => match kline::parse(&raw) {
                Ok(Message::Kline(k)) => {
                    deadline = Instant::now() + silence;
                    *candle_seen = true;
                    match tracker.see(k.candle.timestamp()) {
                        Seen::Next => {}
                        Seen::AfterGap(gap) => events.send(FeedEvent::Gap(gap)).ok()?,
                        Seen::Repeat => continue,
                    }
                    FeedEvent::Kline(k)
                }
                Ok(Message::Reply { error: None, .. }) => continue,
                Ok(Message::Reply { error: Some(e), .. }) => return Some(Reason::Refused(e)),
                Err(error) => FeedEvent::Invalid { raw, error },
            },
            WebsocketEvent::Error(e) if e.contains(GAVE_UP) => return Some(Reason::GaveUp(e)),
            // The SDK reconnects by itself after the rest.
            _ => continue,
        };
        events.send(out).ok()?;
    }
}
