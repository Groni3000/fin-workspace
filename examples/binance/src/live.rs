//! The engine's event source for a live run: the candles of one symbol from [`feed`].
//!
//! A candle's event is stamped with the candle's own time, its open time, as a backtest
//! stamps it, so live and backtest runs over the same candles line up.

use std::fmt::{self, Display};

use binance_sdk::spot::websocket_streams::WebsocketStreamsHandle;
use engine::event::{Event, EventSource, Kind};
use mdata::ohlcv::Ohlcv;
use mdata::{HasTimestamp, HasVolume, Tagged};
use oms::protocol::{Request, RequestSink};
use tokio::sync::mpsc::UnboundedReceiver;
use tradeprim::volume::Volume;

use crate::bridge::{self, Bridge};
use crate::feed::{self, FeedEvent, Watchdog};
use crate::kline::ParseError;

/// Hands out the candles of one symbol as the feed delivers them.
///
/// - Candles without trades are skipped: they repeat the last price.
/// - A message that doesn't parse is a [`Kind::FeedError`] at the current time.
/// - Gaps and reconnects are logged, nothing more.
/// - [`FeedEvent::Lost`] panics: without market data the run can't go on.
///
/// Dropping it stops the feed.
pub struct LiveQueue {
    bridge: Bridge<FeedEvent, ()>,
    /// The time of the last event, ns.
    now: i64,
}

impl LiveQueue {
    /// Starts the feed of `symbol` (as Binance spells it, e.g. `BTCUSDT`) on a thread of its own.
    pub fn start(
        streams: WebsocketStreamsHandle,
        symbol: String,
        watchdog: Watchdog,
    ) -> std::io::Result<Self> {
        let bridge = bridge::spawn(move |events, _: UnboundedReceiver<()>| async move {
            let forever = std::future::pending();
            feed::run(&streams, &symbol, watchdog, &events, forever).await;
        })?;
        Ok(Self { bridge, now: 0 })
    }
}

impl EventSource for LiveQueue {
    type Record = Tagged<Ohlcv>;

    /// Blocks until there is something for the engine. `None` if the feed's thread has ended
    /// without saying why (it panicked; dropping the queue resumes the panic).
    fn next_event(&mut self) -> Option<Event<Tagged<Ohlcv>>> {
        loop {
            match self.bridge.recv().ok()? {
                FeedEvent::Kline(k) => {
                    if k.candle.volume() == Volume::ZERO {
                        continue;
                    }
                    // Candles come in order: the feed drops repeats.
                    self.now = i64::try_from(k.candle.timestamp().as_nanosecond())
                        .expect("a candle time within the i64-nanosecond range (years 1677..2262)");
                    return Some(Event::new(self.now, Kind::MarketData(k.candle)));
                }
                FeedEvent::Invalid { raw, error } => {
                    let error = Box::new(Invalid { raw, error });
                    return Some(Event::new(self.now, Kind::FeedError(error)));
                }
                FeedEvent::Gap(gap) => {
                    tracing::warn!(from = %gap.from, until = %gap.until, "candles missed");
                }
                FeedEvent::Reconnecting { reason, after } => {
                    tracing::warn!(%reason, after = ?after, "reconnecting");
                }
                FeedEvent::Lost { blind, reason } => {
                    panic!("market data lost: no candle for {blind:?}; the last attempt: {reason}")
                }
            }
        }
    }
}

impl RequestSink for LiveQueue {
    fn submit(&mut self, req: Request) {
        panic!("no executor yet, cannot handle {req:?}")
    }
}

/// A message from the feed that didn't parse.
#[derive(Debug)]
struct Invalid {
    raw: String,
    error: ParseError,
}

impl Display for Invalid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid message {:?}: {}", self.raw, self.error)
    }
}

impl std::error::Error for Invalid {}
