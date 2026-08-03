use chrono::{DateTime, Utc};
use instrid::instruments::Instrument;
use oms::fill::Fill;
use std::fmt::Debug;
use uuid::Uuid;

#[derive(Debug)]
pub enum Event {
    Ack(OrderId),
    Fill(Fill),
    Reject(OrderId),
    CancelResponse(OrderId),
    Timer(TimerKind),
    Operator(Command),
}

#[derive(Debug)]
pub struct Scheduled {
    timestamp: i64,
    event: Event,
    seq: u64,
}

impl Scheduled {
    /// Returns the current time as a `DateTime<Utc>` (nanos).
    #[inline]
    pub fn timestamp(&self) -> DateTime<Utc> {
        DateTime::from_timestamp_nanos(self.timestamp)
    }

    pub fn event(&self) -> &Event {
        &self.event
    }

    pub fn seq(&self) -> u64 {
        self.seq
    }
}

impl PartialEq for Scheduled {
    fn eq(&self, other: &Self) -> bool {
        self.timestamp == other.timestamp && self.seq == other.seq
    }
}

impl Eq for Scheduled {}

impl PartialOrd for Scheduled {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.timestamp.partial_cmp(&other.timestamp) {
            Some(core::cmp::Ordering::Equal) => {}
            ord => return ord,
        }
        self.seq.partial_cmp(&other.seq)
    }
}

impl Ord for Scheduled {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap_or(std::cmp::Ordering::Equal)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OrderId(Uuid);

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
