pub mod market_only;
pub mod mkt_stp;

use oms::order::{New, Order};

use crate::{
    event::{Event, Scheduler},
    executors::{market_only::MarketExecutor, mkt_stp::MarketStopExecutor},
    market_data::{Candle, Instrumented},
};

/// Marks type as an executor: it fills/cancels/rejects orders.
pub trait Executor {
    fn on_event<M: Candle + Instrumented>(
        &mut self,
        event: &Event<M>,
        scheduler: &mut Scheduler<'_, M>,
    );
    fn push<M: Candle + Instrumented>(
        &mut self,
        order: Order<New>,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    );
}

impl Executor for MarketExecutor {
    fn on_event<M: Candle + Instrumented>(
        &mut self,
        event: &Event<M>,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        self.on_event(event, scheduler);
    }
    fn push<M: Candle + Instrumented>(
        &mut self,
        order: Order<New>,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        self.push(order, timestamp, scheduler);
    }
}
impl Executor for MarketStopExecutor {
    fn on_event<M: Candle + Instrumented>(
        &mut self,
        event: &Event<M>,
        scheduler: &mut Scheduler<'_, M>,
    ) {
    }
    fn push<M: Candle + Instrumented>(
        &mut self,
        order: Order<New>,
        timestamp: i64,
        scheduler: &mut Scheduler<'_, M>,
    ) {
    }
}
