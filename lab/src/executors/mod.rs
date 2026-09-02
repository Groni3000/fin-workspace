pub mod market_only;
pub mod mkt_stp_lmt;

use crate::{
    event::{Event, Kind, Request, Scheduler},
    // Each executor concrete impl *should be* a superset of previous one.
    // Most of the code *should be* copy-pasted. It's a sign of success, not a bad design.
    //
    // Once I'm confident enough that those executors are basically supersets of previous,
    // more simple ones, I can entirely drop predecessors or leave them as is because they
    // may flag more clearly strategy intention to the user.
    executors::{market_only::MarketExecutor, mkt_stp_lmt::MarketStopLimitExecutor},
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
impl Executor for MarketStopLimitExecutor {
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
