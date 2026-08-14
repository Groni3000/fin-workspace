use std::collections::HashMap;

use chrono::DateTime;
use oms::{
    OrderId,
    fill::Fill,
    order::{New, Order, OrderType, Working},
};

use crate::{
    event::{Kind, Scheduler},
    market_data::{Instrumented, RelevantPrice},
};

/// Simplest executor:
///     * Accepts market orders only
///     * Every fill is fully executed at the last known price
///     * Constant ack/fill/cancel/reject latency
pub struct MarketExecutor {
    unack_orders: HashMap<OrderId, Order<New>>,
    working_orders: Vec<Order<Working>>,
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
            unack_orders: HashMap::new(),
            working_orders: Vec::new(),
            ack_latency,
            fill_latency,
            cancel_latency,
            reject_latency,
        }
    }

    pub fn unack_orders(&self) -> &HashMap<OrderId, Order<New>> {
        &self.unack_orders
    }

    pub fn working_orders(&self) -> &[Order<Working>] {
        &self.working_orders
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
            self.reject(order.order_id(), timestamp, scheduler);
            return;
        }
        if self.unack_orders.contains_key(&order.order_id()) {
            self.reject(order.order_id(), timestamp, scheduler);
            return;
        }
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
        order_id: OrderId,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        // If the order is in unack_orders or working_orders, schedule response with `true`
        if self.unack_orders.contains_key(&order_id)
            || self
                .working_orders()
                .iter()
                .find(|o| o.order_id() == order_id)
                .is_some()
        {
            scheduler.push(
                timestamp + self.cancel_latency as i64,
                Kind::CancelResponse(order_id, true),
            );
            return;
        }
        // If the order is not in unack_orders or working_orders, it's already been cancelled or filled.
        // Schedule response with `false`
        scheduler.push(
            timestamp + self.cancel_latency as i64,
            Kind::CancelResponse(order_id, false),
        );
    }

    /// Schedule a rejection for the given order.
    pub fn reject<M>(
        &mut self,
        order_id: OrderId,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        scheduler.push(
            timestamp + self.reject_latency as i64,
            Kind::Reject(order_id),
        )
    }

    /// For a given instrument from market data record,
    /// schedule a full fill for every order in working orders.
    pub fn on_record<M: RelevantPrice + Instrumented>(
        &mut self,
        md_record: &M,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        self.working_orders.retain(|order| {
            if order.instrument() != md_record.instrument() {
                return true;
            }
            let fill = Fill::new(
                order.order_id(),
                DateTime::from_timestamp_nanos(timestamp),
                order.instrument(),
                order.side(),
                order.quantity(),
                md_record.last_price(),
            );
            scheduler.push(timestamp + self.fill_latency as i64, Kind::Fill(fill));
            false
        });
    }
}

// --- Reactions implementations
impl MarketExecutor {
    /// On arrival of an acknowledgment, moves the order to the working orders.
    pub fn on_ack(&mut self, order_id: &OrderId) {
        if let Some(order) = self.unack_orders.remove(order_id) {
            self.working_orders.push(order.into_working());
        }
    }

    /// On arrival of a Fill, remove order from working orders.
    pub fn on_fill(&mut self, fill: &Fill) {
        let order_id = fill.order_id();
        self.working_orders
            .retain(|order| order.order_id() != order_id);
    }

    pub fn on_reject(&mut self, order_id: &OrderId) {
        match self.unack_orders.remove(order_id) {
            // Successfully removed from unack_orders, no need to remove from working_orders
            Some(_) => {}
            // Order was not found in unack_orders, remove from working_orders
            None => {
                self.working_orders
                    .retain(|order| order.order_id() != *order_id);
            }
        }
    }

    pub fn on_cancel(&mut self, order_id: &OrderId, ok: &bool) {
        if !ok {
            return;
        }
        self.working_orders
            .retain(|order| &order.order_id() != order_id);
        self.unack_orders.remove(order_id);
    }
}
