use chrono::{DateTime, Utc};
use instrid::instruments::Instrument;
use oms::{OrderId, fill::Fill};
use std::fmt::Debug;

#[derive(Debug)]
pub enum Event<T> {
    MarketData(T),
    Ack(OrderId),
    Fill(Fill),
    Reject(OrderId),
    CancelResponse(OrderId),
    Timer(TimerKind),
    Operator(Command),
}

#[derive(Debug)]
pub struct Scheduled<T> {
    timestamp: i64,
    event: Event<T>,
    seq: u64,
}

impl<T> Scheduled<T> {
    /// Returns the current time as a `DateTime<Utc>` (nanos).
    #[inline]
    pub fn timestamp(&self) -> DateTime<Utc> {
        DateTime::from_timestamp_nanos(self.timestamp)
    }

    pub fn event(&self) -> &Event<T> {
        &self.event
    }

    pub fn seq(&self) -> u64 {
        self.seq
    }
}

impl<T> PartialEq for Scheduled<T> {
    fn eq(&self, other: &Self) -> bool {
        self.timestamp == other.timestamp && self.seq == other.seq
    }
}

impl<T> Eq for Scheduled<T> {}

impl<T> Ord for Scheduled<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.timestamp, self.seq)
            .partial_cmp(&(other.timestamp, other.seq))
            .unwrap()
    }
}

impl<T> PartialOrd for Scheduled<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Different kinds of Time based actions based on wall-clock (not driven by market data)
#[derive(Debug)]
pub enum TimerKind {
    /// If cancel request haven't been acknowledged/failed, wait and retry.
    CancelRetry(OrderId),
    /// Contract is near expiration/poor-liquidity, roll to the next contract.
    ContractRoll(Instrument),
    /// Safe to close session candle aggregation or some other things.
    SessionClose,
    /// Publish a snapshot of the current state.
    PublishSnapshot,
    /// Feed is stale - used for notifications.
    FeedStale,
    // More to come?
}

/// Commands manually sent by the Operator to the trading engine.
#[derive(Debug)]
pub enum Command {
    /// Liquidate all open positions.
    LiquidateAll,
    /// Strategy doesn't generate new orders.
    Kill,
}
