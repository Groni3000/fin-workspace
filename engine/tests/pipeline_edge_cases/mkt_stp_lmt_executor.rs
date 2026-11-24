//! Over `SimQueue` and `MarketStopLimitExecutor`: a market order fills at the next candle's
//! open; a limit order fills, in full, on the first candle that trades through its price.

use engine::sim::{MarketStopLimitExecutor, SimQueue};
use oms::{manager::Oms, portfolio::Portfolio, rms::NaiveRms};

use crate::common::{Step, candles, run_resting};

mod cancel_too_late;

const ACK: u64 = 200_000_000;
const FILL: u64 = 250_000_000;
/// Shorter than `FILL`: a refused cancel gets back before the fill that made it too late.
const CANCEL: u64 = 100_000_000;
const REJECT: u64 = 100_000_000;

/// Runs [`ScriptedResting`](crate::common) over `ohlc` (one candle a minute), one step per
/// candle, and returns its trace, the OMS and the final portfolio.
pub fn run_steps(ohlc: &[[&str; 4]], steps: &[Step]) -> (Vec<String>, Oms, Portfolio) {
    let exec = MarketStopLimitExecutor::new(ACK, FILL, CANCEL, REJECT);
    run_resting(
        SimQueue::new(candles(ohlc).into_iter(), exec),
        steps,
        &NaiveRms,
    )
}
