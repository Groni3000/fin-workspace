//! An order sent on the last candle: the data ends before there is a next open to fill it at.
//! The ack still arrives, the fill never does, and the order is left working.

use super::run_script;
use crate::common::{position, spy};

#[test]
fn a_buy_sent_on_the_last_candle_is_left_working() {
    let (trace, oms, pf) = run_script(&["100", "101", "102"], &[0, 0, 1]);

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 0",
            "02:00.000  candle 101, held 0, want 0",
            "03:00.000  candle 102, held 0, want 1",
            "03:00.000  send Market Buy 1",
            "03:00.200  ack",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(0));
    assert!(pf.fills().is_empty());
    assert!(!oms.is_empty(), "the buy is still working");
}

#[test]
fn an_exit_sent_on_the_last_candle_leaves_the_position_open() {
    let (trace, oms, pf) = run_script(&["100", "101", "102"], &[1, 1, 0]);

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 1",
            "01:00.000  send Market Buy 1",
            "01:00.200  ack",
            "02:00.000  candle 101, held 0, want 1",
            "02:00.200  fill Buy 1 @ 101, held 1",
            "03:00.000  candle 102, held 1, want 0",
            "03:00.000  send Market Sell 1",
            "03:00.200  ack",
        ]
    );
    // Long, although the strategy's last decision was flat: the sell never filled.
    assert_eq!(pf.position(&spy()), &position(1));
    assert!(!oms.is_empty(), "the sell is still working");
}
