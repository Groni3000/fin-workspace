use std::collections::{HashMap, hash_map::Entry};

use chrono::DateTime;
use instrid::instruments::Instrument;
use oms::{
    OrderId,
    fill::Fill,
    order::{New, Order, OrderType, Working},
};
use tradeprim::{Side, price::Price};

use crate::{
    event::{Kind, RejectReason, Scheduler},
    market_data::{Candle, Instrumented},
};

/// Natural extension of `MarketExecutor`:
///     * Accepts market+stop orders only
///     * Every fill is fully executed
///     * Constant ack/fill/cancel/reject latency
pub struct MarketStopLimitExecutor {
    /// Executor got an order, yet it's not tradable yet. May be rejected.
    pending_orders: HashMap<OrderId, Order<New>>,
    /// Executor is trying to fill these orders.
    working_orders: HashMap<Instrument, Vec<Order<Working>>>,
    ack_latency: u64,
    fill_latency: u64,
    cancel_latency: u64,
    reject_latency: u64,
}

impl MarketStopLimitExecutor {
    pub fn new(
        ack_latency: u64,
        fill_latency: u64,
        cancel_latency: u64,
        reject_latency: u64,
    ) -> Self {
        let pending_orders = HashMap::new();
        let working_orders = HashMap::new();
        Self {
            pending_orders,
            working_orders,
            ack_latency,
            fill_latency,
            cancel_latency,
            reject_latency,
        }
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
impl MarketStopLimitExecutor {
    /// Pushes a market or stop order to the executor.
    ///
    /// Rejects the order if:
    ///     - it is not a market/stop order.
    ///     - it's already in unacknowledged orders
    ///
    /// Schedules acknowledgment.
    pub fn push<M>(&mut self, order: Order<New>, timestamp: i64, scheduler: &mut Scheduler<'_, M>) {
        match order.order_type() {
            OrderType::Market | OrderType::Stop(_) | OrderType::Limit(_) => {}
            _ => {
                self.reject(
                    order.order_id(),
                    RejectReason::UnsupportedOrderType(*order.order_type()),
                    timestamp,
                    scheduler,
                );
                return;
            }
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

    /// Cancels order and schedules cancellation message arrival of an order by its id.
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

    /// Fills every working order for this record's instrument: market orders at
    /// the last price, triggered stops at their trigger, worsened to the bar's
    /// open when the bar gapped through the trigger price.
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
            // Guards
            let fill_price = match order.order_type() {
                OrderType::Market => md_record.open(),
                OrderType::Stop(stp_price) => match order.side() {
                    Side::Buy => {
                        if md_record.high() < *stp_price {
                            return true;
                        }
                        *stp_price.max(&md_record.open())
                    }
                    Side::Sell => {
                        if md_record.low() > *stp_price {
                            return true;
                        }
                        *stp_price.min(&md_record.open())
                    }
                },
                OrderType::Limit(limit_price) => match order.side() {
                    Side::Buy => {
                        if md_record.low() > *limit_price {
                            return true;
                        }
                        *limit_price.min(&md_record.open())
                    }
                    Side::Sell => {
                        if md_record.high() < *limit_price {
                            return true;
                        }
                        *limit_price.max(&md_record.open())
                    }
                },
                _ => unreachable!("Not supported order type: {}", order.order_type()),
            };

            // All guards passed => schedule a fully filled order
            let fill = Self::get_fill_to_fully_fill_the_order(timestamp, order, fill_price);
            scheduler.push(timestamp + self.fill_latency as i64, Kind::Fill(fill));

            false
        });

        if working_orders.get().is_empty() {
            working_orders.remove();
        }
    }

    fn get_fill_to_fully_fill_the_order(
        timestamp: i64,
        order: &Order<Working>,
        fill_price: Price,
    ) -> Fill {
        Fill::new(
            order.order_id(),
            DateTime::from_timestamp_nanos(timestamp),
            order.instrument(),
            order.side(),
            order.quantity(),
            fill_price,
        )
    }
}

// --- Reactions implementations
impl MarketStopLimitExecutor {
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
