pub mod market_only;
pub mod mkt_stp;

use crate::{
    event::{Event, Kind, Request, Scheduler},
    executors::{market_only::MarketExecutor, mkt_stp::MarketStopExecutor},
    market_data::{Candle, Instrumented},
};

// TODO: generic Latency models for executors

/// Marks type as an executor: it fills/cancels/rejects orders.
pub trait Executor {
    fn on_event<M: Candle + Instrumented>(
        &mut self,
        event: &Event<M>,
        scheduler: &mut Scheduler<'_, M>,
    );
    fn on_request<M>(&mut self, timestamp: i64, request: Request, scheduler: &mut Scheduler<'_, M>);
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
            Kind::Reject(order_id) => self.on_reject(order_id),
            Kind::CancelResponse(order_id, ok) => self.on_cancel(order_id, ok),
            Kind::FeedError(_) => {}
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
            Request::CancelOrder(order_id) => self.cancel(order_id, timestamp, scheduler),
            Request::Snapshot => {}
        }
    }
}
impl Executor for MarketStopExecutor {
    fn on_event<M: Candle + Instrumented>(
        &mut self,
        event: &Event<M>,
        scheduler: &mut Scheduler<'_, M>,
    ) {
    }
    fn on_request<M>(
        &mut self,
        timestamp: i64,
        request: Request,
        scheduler: &mut Scheduler<'_, M>,
    ) {
    }
}
