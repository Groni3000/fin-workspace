use mdata::{Candle, Instrumented};

use oms::protocol::Request;

use crate::event::{Event, Scheduler};

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
