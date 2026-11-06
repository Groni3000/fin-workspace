use std::collections::hash_map::Entry;

use foldhash::{HashMap, HashMapExt};

use chrono::DateTime;
use instrid::instruments::Instrument;
use oms::{
    OrderId,
    fill::Fill,
    order::{New, Order, OrderType, Working},
};

use mdata::{Candle, Instrumented};

use crate::{
    event::{Event, Kind, RejectReason, Request, Scheduler},
    executor::Executor,
};

/// Simplest executor:
///     * Accepts market orders only
///     * Every fill is fully executed at the *open* of the first record after the order works,
///       not its close. The lower frequency (1s -> 1m -> ...) the worse to use *close*.
///     * Constant ack/fill/cancel/reject latency
pub struct MarketExecutor {
    /// Executor got an order, yet it's not tradable yet. May be rejected.
    pending_orders: HashMap<OrderId, Order<New>>,
    /// Executor is trying to fill these orders.
    working_orders: HashMap<Instrument, Vec<Order<Working>>>,
    ack_latency: u64,
    fill_latency: u64,
    cancel_latency: u64,
    reject_latency: u64,
}

impl MarketExecutor {
    pub fn new(
        ack_latency: u64,
        fill_latency: u64,
        cancel_latency: u64,
        reject_latency: u64,
    ) -> Self {
        Self {
            pending_orders: HashMap::new(),
            working_orders: HashMap::new(),
            ack_latency,
            fill_latency,
            cancel_latency,
            reject_latency,
        }
    }

    pub fn pending_orders(&self) -> &HashMap<OrderId, Order<New>> {
        &self.pending_orders
    }

    pub fn working_orders(&self) -> &HashMap<Instrument, Vec<Order<Working>>> {
        &self.working_orders
    }

    /// Drops the order from its instrument's book, dropping the book itself when it empties.
    fn drop_working(&mut self, instrument: Instrument, order_id: OrderId) -> bool {
        let Entry::Occupied(mut working_orders) = self.working_orders.entry(instrument) else {
            return false;
        };
        let n = working_orders.get().len();
        working_orders
            .get_mut()
            .retain(|o| o.order_id() != order_id);
        let dropped = working_orders.get().len() != n;
        if working_orders.get().is_empty() {
            working_orders.remove();
        }
        dropped
    }
}

// --- Scheduling operations
impl MarketExecutor {
    /// Pushes a market order to the executor.
    ///
    /// Rejects the order if:
    ///     - it is not a market order.
    ///     - it's already in unacknowledged orders
    ///
    /// Schedules acknowledgment.
    pub fn push<M>(&mut self, order: Order<New>, timestamp: i64, scheduler: &mut Scheduler<'_, M>) {
        if order.order_type() != &OrderType::Market {
            self.reject(
                order.order_id(),
                RejectReason::UnsupportedOrderType(*order.order_type()),
                timestamp,
                scheduler,
            );
            return;
        }
        if self.pending_orders.contains_key(&order.order_id()) {
            self.reject(
                order.order_id(),
                RejectReason::DuplicateOrderId,
                timestamp,
                scheduler,
            );
            return;
        }
        self.pending_orders.insert(order.order_id(), order);
        self.acknowledge(order.order_id(), timestamp, scheduler);
    }

    /// Schedules acknowledgment for the order.
    pub fn acknowledge<M>(
        &mut self,
        order_id: OrderId,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        scheduler.push(timestamp + self.ack_latency as i64, Kind::Ack(order_id));
    }

    /// Schedules cancellation of an order by its id.
    pub fn cancel<M>(
        &mut self,
        instrument: Instrument,
        order_id: OrderId,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        let existed = self.pending_orders.remove(&order_id).is_some();
        let existed = existed || self.drop_working(instrument, order_id);
        scheduler.push(
            timestamp + self.cancel_latency as i64,
            Kind::CancelResponse(order_id, existed),
        );
    }

    /// Schedule a rejection for the given order.
    pub fn reject<M>(
        &mut self,
        order_id: OrderId,
        reason: RejectReason,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        scheduler.push(
            timestamp + self.reject_latency as i64,
            Kind::Reject(order_id, reason),
        )
    }

    /// For a given instrument from market data record,
    /// schedule a full fill at its open for every order in working orders.
    pub fn on_record<M: Candle + Instrumented>(
        &mut self,
        md_record: &M,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        let instrument = md_record.instrument();
        let Entry::Occupied(mut working_orders) = self.working_orders.entry(instrument) else {
            return;
        };
        working_orders.get_mut().retain(|order| {
            let fill = Fill::new(
                order.order_id(),
                DateTime::from_timestamp_nanos(timestamp),
                order.instrument(),
                order.side(),
                order.quantity(),
                md_record.open(),
            );
            scheduler.push(timestamp + self.fill_latency as i64, Kind::Fill(fill));
            false
        });

        if working_orders.get().is_empty() {
            working_orders.remove();
        }
    }
}

// --- Reactions implementations
impl MarketExecutor {
    /// On arrival of an acknowledgment, moves the order to the working orders.
    pub fn on_ack(&mut self, order_id: &OrderId) {
        if let Some(order) = self.pending_orders.remove(order_id) {
            self.working_orders
                .entry(order.instrument())
                .or_default()
                .push(order.into_working());
        }
    }

    /// On arrival of a Fill, remove order from working orders.
    pub fn on_fill(&mut self, fill: &Fill) {
        self.drop_working(fill.instrument(), fill.order_id());
    }

    pub fn on_reject(&mut self, order_id: &OrderId, reason: &RejectReason) {
        match reason {
            // Never was in pending orders
            RejectReason::UnsupportedOrderType(_ord_type) => {
                return;
            }
            // Never was in pending orders
            RejectReason::DuplicateOrderId => {
                return;
            }
            // Live reason
            RejectReason::Venue(_str_reason) => {}
        }
        match self.pending_orders.remove(order_id) {
            // Successfully removed from pending_orders, no need to remove from working_orders
            Some(_) => {}
            // Order was not found in pending_orders
            None => {
                unreachable!("Order not found in pending_orders: {:?}", order_id)
            }
        }
    }

    /// No-op, - venue has already cancelled an order
    pub fn on_cancel(&mut self, _order_id: &OrderId, _ok: &bool) {}

    /// No-op, - venue has already expired an order
    pub fn on_expire(&mut self, _order_id: &OrderId) {}
}

impl Executor for MarketExecutor {
    fn on_event<M: Candle + Instrumented>(
        &mut self,
        event: &Event<M>,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        match event.kind() {
            Kind::MarketData(md_record) => self.on_record(md_record, event.ts(), scheduler),
            Kind::Ack(order_id) => self.on_ack(order_id),
            Kind::Fill(fill) => self.on_fill(fill),
            Kind::Reject(order_id, reason) => self.on_reject(order_id, reason),
            Kind::CancelResponse(order_id, ok) => self.on_cancel(order_id, ok),
            Kind::FeedError(_) => {}
            Kind::Expired(_instrument, order_id) => self.on_expire(order_id),
        }
    }
    fn on_request<M>(
        &mut self,
        timestamp: i64,
        request: Request,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        match request {
            Request::SendOrder(order) => self.push(order, timestamp, scheduler),
            Request::CancelOrder(instrument, order_id) => {
                self.cancel(instrument, order_id, timestamp, scheduler)
            }
            Request::Snapshot => {}
        }
    }
}

#[cfg(test)]
mod tests;
