//! Over `SimQueue` and a venue that refuses to cancel an order it hasn't accepted yet: until
//! the ack, the order is still on its way and the venue doesn't know it. Otherwise it behaves
//! like `MarketStopLimitExecutor`, which it wraps.

use engine::{
    event::{Event, Kind, Scheduler},
    executor::Executor,
    sim::{MarketStopLimitExecutor, SimQueue},
};
use mdata::{Candle, HasInstrument};
use oms::{
    manager::Oms,
    portfolio::Portfolio,
    protocol::{ExecEvent, Request},
    rms::NaiveRms,
};

use crate::common::{Step, candles, run_resting};

mod cancel_overtakes_the_order;

/// Slower than a candle (one a minute): a strategy can drop its order on the next candle,
/// before the venue has accepted it.
const ACK: u64 = 60_250_000_000;
const FILL: u64 = 250_000_000;
const CANCEL: u64 = 100_000_000;
const REJECT: u64 = 100_000_000;

struct RefusesUnackedCancels {
    inner: MarketStopLimitExecutor,
}

impl Executor for RefusesUnackedCancels {
    fn on_event<M: Candle + HasInstrument>(
        &mut self,
        event: &Event<M>,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        self.inner.on_event(event, scheduler);
    }

    fn on_request<M>(
        &mut self,
        timestamp: i64,
        request: Request,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        match request {
            Request::CancelOrder(_, id) if self.inner.pending_orders().contains_key(&id) => {
                scheduler.push(
                    timestamp + CANCEL as i64,
                    Kind::Exec(ExecEvent::CancelResponse(id, false)),
                );
            }
            other => self.inner.on_request(timestamp, other, scheduler),
        }
    }
}

/// Runs [`ScriptedResting`](crate::common) over `ohlc` (one candle a minute), one step per
/// candle, and returns its trace, the OMS and the final portfolio.
pub fn run_steps(ohlc: &[[&str; 4]], steps: &[Step]) -> (Vec<String>, Oms, Portfolio) {
    let exec = RefusesUnackedCancels {
        inner: MarketStopLimitExecutor::new(ACK, FILL, CANCEL, REJECT),
    };
    run_resting(
        SimQueue::new(candles(ohlc).into_iter(), exec),
        steps,
        &NaiveRms,
    )
}
