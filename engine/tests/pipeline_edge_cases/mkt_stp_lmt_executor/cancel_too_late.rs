//! The strategy drops its limit order on the candle that fills it. The executor has already
//! filled the order when the cancel gets there, so it refuses the cancel, and the refusal
//! arrives before the fill.

use super::run_steps;
use crate::common::{Step, position, spy};
use tradeprim::Side;

#[test]
fn a_refused_cancel_is_retried_until_the_fill_and_the_fill_is_sold_back() {
    let (trace, oms, pf) = run_steps(
        &[
            // Each row is a Candle
            ["100", "100", "100", "100"],
            ["100", "100", "98", "99"],
            ["99", "99", "99", "99"],
            ["99", "99", "99", "99"],
        ],
        &[
            Step::Place(Side::Buy, "99"),
            Step::Drop,
            Step::Wait,
            Step::Wait,
        ],
    );

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100/100/100/100, held 0, place Buy 1 @ 99",
            "01:00.000  send Limit 99 Buy 1",
            "01:00.200  ack",
            // The executor fills the order on this candle, before the strategy drops it.
            "02:00.000  candle 100/100/98/99, held 0, drop",
            "02:00.000  send cancel",
            "02:00.100  WARN cancel refused, retrying while the order is live",
            "02:00.100  cancel refused",
            "02:00.100  send cancel",
            "02:00.200  WARN cancel refused, retrying while the order is live",
            "02:00.200  cancel refused",
            "02:00.200  send cancel",
            // The fill: the strategy dropped the order, so it still wants to be flat.
            "02:00.250  fill Buy 1 @ 99, held 1",
            "02:00.250  send Market Sell 1",
            // The last retry's refusal, after the fill ended the order.
            "02:00.300  WARN cancel response not found in pending cancels",
            "02:00.300  cancel refused",
            "02:00.450  ack",
            "03:00.000  candle 99/99/99/99, held 1, wait",
            "03:00.250  fill Sell 1 @ 99, held 0",
            "04:00.000  candle 99/99/99/99, held 0, wait",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(0));
    assert!(oms.is_empty(), "nothing left in flight");
}
