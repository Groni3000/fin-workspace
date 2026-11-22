//! The strategy changes its mind while a market order is still working. The OMS never
//! cancels a market order: it sends the difference between what's wanted and what's held
//! plus what's in flight, so the order is offset at once.

use super::run_script;
use crate::common::{position, spy};

#[test]
fn flat_again_before_the_buy_fills_sells_it_at_once() {
    let (trace, oms, pf) = run_script(&["100", "101", "102", "103"], &[1, 0, 0, 0]);

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 1",
            "01:00.000  send Market Buy 1",
            "01:00.200  ack",
            "02:00.000  candle 101, held 0, want 0",
            "02:00.000  send Market Sell 1",
            "02:00.200  fill Buy 1 @ 101, held 1",
            "02:00.200  ack",
            "03:00.000  candle 102, held 1, want 0",
            "03:00.200  fill Sell 1 @ 102, held 0",
            "04:00.000  candle 103, held 0, want 0",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(0));
    assert!(oms.is_empty(), "nothing left in flight");
}

#[test]
fn back_and_forth_before_anything_fills_sends_one_order_per_change() {
    let (trace, oms, pf) = run_script(&["100", "101", "102", "103", "104"], &[1, 0, 1, 1, 1]);

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 1",
            "01:00.000  send Market Buy 1",
            "01:00.200  ack",
            "02:00.000  candle 101, held 0, want 0",
            "02:00.000  send Market Sell 1",
            "02:00.200  fill Buy 1 @ 101, held 1",
            "02:00.200  ack",
            "03:00.000  candle 102, held 1, want 1",
            "03:00.000  send Market Buy 1",
            "03:00.200  fill Sell 1 @ 102, held 0",
            "03:00.200  ack",
            "04:00.000  candle 103, held 0, want 1",
            "04:00.200  fill Buy 1 @ 103, held 1",
            "05:00.000  candle 104, held 1, want 1",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(1));
    assert!(oms.is_empty(), "nothing left in flight");
}
