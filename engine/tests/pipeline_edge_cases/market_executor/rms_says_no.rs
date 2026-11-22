//! The RMS standing between what the strategy wants and what the OMS sends.

use oms::rms::{HaltedRms, MaxPositionRms};
use tradeprim::quantity::Quantity;

use super::run_script_with;
use crate::common::{position, spy};

const OPENS: [&str; 6] = ["100", "101", "102", "103", "104", "105"];

fn max_1() -> MaxPositionRms {
    MaxPositionRms::new(
        Quantity::from_str_unchecked("1")
            .non_zero()
            .expect("non-zero quantity"),
    )
}

/// Strategy wants 2, Rms allows max 1, so Oms sends 1.
///
/// No warnings: the clamp is checked after every event, so it logs nothing itself, or it would
/// repeat on every one. It's logged once, on the order it shapes: the exec log's "send market
/// order" line carries `want` (2) next to `dp` (1). Once at the cap nothing more is sent, so
/// nothing more is logged: the position doesn't change, and the strategy can see from its
/// portfolio that it holds less than it wants.
#[test]
fn a_cap_of_1_buys_1_when_the_strategy_wants_2_and_asks_no_more() {
    let (trace, oms, pf) = run_script_with(&OPENS, &[2, 2, 2, 2, 2, 2], &max_1());

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 2",
            "01:00.000  send Market Buy 1",
            "01:00.200  ack",
            "02:00.000  candle 101, held 0, want 2",
            "02:00.200  fill Buy 1 @ 101, held 1",
            "03:00.000  candle 102, held 1, want 2",
            "04:00.000  candle 103, held 1, want 2",
            "05:00.000  candle 104, held 1, want 2",
            "06:00.000  candle 105, held 1, want 2",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(1));
    assert!(oms.is_empty(), "nothing left in flight");
}

/// The cap allows short 1, so the OMS sends `Sell 2`: bigger than the cap, but the position
/// it leads to (-1) is within it, and that's what the RMS judges.
#[test]
fn a_cap_of_1_allows_a_reversal_from_long_1_to_short_1() {
    let (trace, oms, pf) = run_script_with(&OPENS, &[1, 1, -1, -1, -1, -1], &max_1());

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 1",
            "01:00.000  send Market Buy 1",
            "01:00.200  ack",
            "02:00.000  candle 101, held 0, want 1",
            "02:00.200  fill Buy 1 @ 101, held 1",
            "03:00.000  candle 102, held 1, want -1",
            "03:00.000  send Market Sell 2",
            "03:00.200  ack",
            "04:00.000  candle 103, held 1, want -1",
            "04:00.200  fill Sell 2 @ 103, held -1",
            "05:00.000  candle 104, held -1, want -1",
            "06:00.000  candle 105, held -1, want -1",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(-1));
    assert!(oms.is_empty(), "nothing left in flight");
}

#[test]
fn halted_sends_nothing() {
    let (trace, oms, pf) = run_script_with(&OPENS, &[1, 1, 1, 1, 1, 1], &HaltedRms);

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 1",
            "02:00.000  candle 101, held 0, want 1",
            "03:00.000  candle 102, held 0, want 1",
            "04:00.000  candle 103, held 0, want 1",
            "05:00.000  candle 104, held 0, want 1",
            "06:00.000  candle 105, held 0, want 1",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(0));
    assert!(oms.is_empty(), "nothing left in flight");
}
