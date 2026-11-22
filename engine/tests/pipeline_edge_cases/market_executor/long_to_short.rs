//! From long to short in one step: one sell for the whole difference, crossing zero in a
//! single fill.

use super::run_script;
use crate::common::{position, spy};

#[test]
fn long_1_to_short_1_is_one_sell_for_2() {
    let (trace, oms, pf) = run_script(&["100", "101", "102", "103", "104"], &[1, 1, -1, -1, -1]);

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
        ]
    );
    assert_eq!(pf.position(&spy()), &position(-1));
    assert!(oms.is_empty(), "nothing left in flight");
}

#[test]
fn long_2_to_short_1_before_the_buy_fills_is_one_sell_for_3() {
    let (trace, oms, pf) = run_script(&["100", "101", "102", "103"], &[2, -1, -1, -1]);

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100, held 0, want 2",
            "01:00.000  send Market Buy 2",
            "01:00.200  ack",
            "02:00.000  candle 101, held 0, want -1",
            "02:00.000  send Market Sell 3",
            "02:00.200  fill Buy 2 @ 101, held 2",
            "02:00.200  ack",
            "03:00.000  candle 102, held 2, want -1",
            "03:00.200  fill Sell 3 @ 102, held -1",
            "04:00.000  candle 103, held -1, want -1",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(-1));
    assert!(oms.is_empty(), "nothing left in flight");
}
