//! The event loop: one function that drives a strategy through a queue.

use oms::{manager::Oms, portfolio::Portfolio, rms::Rms};

use crate::{
    event::{EventSource, Kind},
    strategy::Traded,
    telemetry::SimClock,
};

/// Runs `strategy` over every event of `queue`, until the queue is empty. For each event:
///
/// 1. `clock` is set to the event's time, so log lines carry it.
/// 2. An executor's event goes to the OMS first, so `pf` already holds a fill when...
/// 3. ...the strategy sees the event and updates what it wants.
/// 4. The OMS closes the gap between what the strategy wants and what's held or working,
///    sending its requests to `queue`.
///
/// Returns the OMS and the portfolio as they are at the end.
///
/// Backtests and replays only, for now.
///
/// In live trading real time data can lag. So when we fall behind
/// wall clock, we need to switch to simulated executor and when
/// we get caught back - we switch to live one. That is not present right now.
pub fn run<Q, S, R>(
    queue: &mut Q,
    strategy: &mut S,
    mut oms: Oms,
    mut pf: Portfolio,
    rms: &R,
    clock: &SimClock,
) -> (Oms, Portfolio)
where
    Q: EventSource,
    S: Traded<Q::Record>,
    R: Rms,
{
    while let Some(event) = queue.next_event() {
        clock.set(event.ts());

        if let Kind::Exec(exec) = event.kind() {
            oms.on_exec(exec, &mut pf);
        }
        strategy.on_event(&event, &pf);

        oms.reconcile(strategy.desired(), &pf, rms, queue);
    }
    (oms, pf)
}
