//! The order protocol between the trading side (strategy, OMS) and an executor:
//! [`Request`]s going out, [`ExecEvent`]s coming back. No market data here, so
//! nothing in it is generic over a record type.

use instrid::instruments::Instrument;

use crate::{
    OrderId,
    fill::Fill,
    order::{New, Order, OrderType},
};

/// What an executor reports about an order.
#[derive(Debug)]
pub enum ExecEvent {
    Ack(OrderId),
    Fill(Fill),
    Reject(OrderId, RejectReason),
    /// `true` if the order was cancelled, `false` if it was already gone (filled,
    /// cancelled or never known).
    CancelResponse(OrderId, bool),
    Expired(Instrument, OrderId),
}

impl ExecEvent {
    /// The order this event is about. Every event is about exactly one order.
    pub fn order_id(&self) -> OrderId {
        match self {
            ExecEvent::Ack(id)
            | ExecEvent::Reject(id, _)
            | ExecEvent::CancelResponse(id, _)
            | ExecEvent::Expired(_, id) => *id,
            ExecEvent::Fill(fill) => fill.order_id(),
        }
    }
}

#[derive(Debug)]
pub enum RejectReason {
    UnsupportedOrderType(OrderType),
    DuplicateOrderId,
    /// Free text for a live trading.
    Venue(String),
}

/// What the trading side asks an executor to do.
#[derive(Debug)]
pub enum Request {
    SendOrder(Order<New>),
    CancelOrder(Instrument, OrderId),
    /// (Timer, fire at ts)
    // StartTimer(TimerKind, i64),
    // CancelTimer(TimerKind),
    Snapshot,
}

/// Anything that accepts [`Request`]s: an event queue, or a mock that only
/// records what was sent.
pub trait RequestSink {
    fn submit(&mut self, req: Request);
}

#[cfg(test)]
mod tests;
