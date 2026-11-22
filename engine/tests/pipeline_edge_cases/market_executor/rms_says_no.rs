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

/// Current behavior produces noise (the `WARN` lines).
///
/// Strategy wants 2, Rms allows max 1, so Oms sends 1.
/// On every event, the first one included, Rms logs that it
/// clamped the wanted position.
#[test]
fn a_cap_of_1_buys_1_when_the_strategy_wants_2_and_asks_no_more() {
    let (trace, oms, pf) = run_script_with(&OPENS, &[2, 2, 2, 2, 2, 2], &max_1());

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 2",
            "01:00.000  WARN rms clamped desired position",
            "01:00.000  send Market Buy 1",
            "01:00.200  ack",
            "01:00.200  WARN rms clamped desired position",
            "02:00.000  candle 101, held 0, want 2",
            "02:00.000  WARN rms clamped desired position",
            "02:00.200  fill Buy 1 @ 101, held 1",
            "02:00.200  WARN rms clamped desired position",
            "03:00.000  candle 102, held 1, want 2",
            "03:00.000  WARN rms clamped desired position",
            "04:00.000  candle 103, held 1, want 2",
            "04:00.000  WARN rms clamped desired position",
            "05:00.000  candle 104, held 1, want 2",
            "05:00.000  WARN rms clamped desired position",
            "06:00.000  candle 105, held 1, want 2",
            "06:00.000  WARN rms clamped desired position",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(1));
    assert!(oms.is_empty(), "nothing left in flight");
}

/// KNOWN BUG, pinned as it behaves today. The cap allows short 1, so the OMS builds
/// `Sell 2`; `MaxPositionRms::approve_order` checks the order's size (2 > 1) instead of the
/// position it leads to (-1), and refuses it on every candle. The strategy wants to be short
/// and stays long, with a warning on every candle. Once fixed, expect `send Market Sell 2` at
/// 03:00 and a short 1 at the end.
#[test]
fn a_cap_of_1_blocks_a_reversal_from_long_1_to_short_1() {
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
            "03:00.000  WARN rms rejected desired order",
            "04:00.000  candle 103, held 1, want -1",
            "04:00.000  WARN rms rejected desired order",
            "05:00.000  candle 104, held 1, want -1",
            "05:00.000  WARN rms rejected desired order",
            "06:00.000  candle 105, held 1, want -1",
            "06:00.000  WARN rms rejected desired order",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(1));
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
