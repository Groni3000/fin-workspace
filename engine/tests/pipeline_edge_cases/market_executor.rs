//! Over `SimQueue` and `MarketExecutor`: a market order fills in full at the next candle's
//! open.

use chrono::DateTime;
use engine::sim::{MarketExecutor, SimQueue};
use mdata::{Ohlcv, Tagged};
use oms::{
    manager::Oms,
    portfolio::Portfolio,
    rms::{NaiveRms, Rms},
};
use tradeprim::{price::Price, volume::Volume};

use crate::common::{Record, run_scripted, spy};

mod change_of_mind;
mod last_candle;
mod long_to_short;
mod rms_says_no;

/// 200ms
const LATENCY: u64 = 200_000_000;

/// Provide valid prices and signed lots your strategy
/// wants to own at the respective moment of time.
///
/// At moment `T_i` the candle opens at `P_i` and the strategy then wants `L_i` lots.
///
/// `MarketExecutor` fills the difference at `T_{i+1}` plus `LATENCY`, at that candle's open
/// `P_{i+1}`.
///
/// This function will run the scripted strategy
/// and return its trace, the OMS and the final portfolio.
pub fn run_script(opens: &[&str], wanted_lots: &[i64]) -> (Vec<String>, Oms, Portfolio) {
    run_script_with(opens, wanted_lots, &NaiveRms)
}

/// [`run_script`] with a given RMS instead of `NaiveRms`.
pub fn run_script_with<R: Rms>(
    opens: &[&str],
    wanted_lots: &[i64],
    rms: &R,
) -> (Vec<String>, Oms, Portfolio) {
    let md: Vec<Result<Record, std::io::Error>> = opens
        .iter()
        .zip(1..)
        .map(|(open, minute)| {
            let px = Price::from_str_unchecked(open);
            let ts = DateTime::from_timestamp(minute * 60, 0).expect("valid timestamp");
            Ok(Tagged::new(
                spy(),
                Ohlcv::new(ts, px, px, px, px, Volume::ZERO),
            ))
        })
        .collect();
    let exec = MarketExecutor::new(LATENCY, LATENCY, LATENCY, LATENCY);
    run_scripted(SimQueue::new(md.into_iter(), exec), wanted_lots, rms)
}
