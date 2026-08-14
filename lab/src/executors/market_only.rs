use std::collections::HashMap;

use oms::{
    OrderId,
    fill::Fill,
    order::{New, Order, OrderType, Working},
};

use crate::{
    event::{Event, Kind, Scheduler},
    market_data::{Instrumented, RelevantPrice},
};

/// Fills everything at last known price at once.
///
/// Supports only Market orders, no TiF checks
pub struct MarketExecutor {
    unack_orders: HashMap<OrderId, Order<New>>,
    working_orders: Vec<Order<Working>>,
    ack_latency: u64,
    fill_latency: u64,
}

impl MarketExecutor {
    pub fn new(ack_latency: u64, fill_latency: u64) -> Self {
        Self {
            unack_orders: HashMap::new(),
            working_orders: Vec::new(),
            ack_latency,
            fill_latency,
        }
    }

    pub fn on_ack(&mut self, order_id: &OrderId) {
        if let Some(order) = self.unack_orders.remove(order_id) {
            self.working_orders.push(order.into_working());
        }
    }

    /// Pushes a market order to the executor.
    pub fn push<M>(&mut self, order: Order<New>, timestamp: i64, scheduler: &mut Scheduler<'_, M>) {
        if order.order_type() != &OrderType::Market {
            panic!("Only market orders are supported");
        }
        if self.unack_orders.insert(order.order_id(), order).is_some() {
            panic!("Order already exists")
        }
        scheduler.push(
            timestamp + self.ack_latency as i64,
            Kind::Ack(order.order_id()),
        );
    }

    pub fn working_orders(&self) -> &[Order<Working>] {
        &self.working_orders
    }

    pub fn on_event<M: RelevantPrice + Instrumented>(
        &mut self,
        event: &Event<M>,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        match event.kind() {
            Kind::MarketData(md_record) => {
                self.on_record(md_record, event.ts() + self.fill_latency as i64, scheduler)
            }
            Kind::Ack(order_id) => self.on_ack(order_id),
            Kind::Fill(fill) => self.on_fill(fill),
            Kind::Reject(_order_id) => {}
            Kind::CancelResponse(_order_id, true) => {}
            Kind::CancelResponse(_order_id, false) => {}
            Kind::FeedError(_err) => {}
        }
    }

    pub fn on_fill(&mut self, fill: &Fill) {
        let order_id = fill.order_id();
        self.working_orders
            .retain(|order| order.order_id() != order_id);
    }

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
                md_record.timestamp(),
                order.instrument(),
                order.side(),
                order.quantity(),
                md_record.last_price(),
            );
            scheduler.push(timestamp, Kind::Fill(fill));
            false
        });
    }

    pub fn ack_latency(&self) -> u64 {
        self.ack_latency
    }

    pub fn fill_latency(&self) -> u64 {
        self.fill_latency
    }
}
