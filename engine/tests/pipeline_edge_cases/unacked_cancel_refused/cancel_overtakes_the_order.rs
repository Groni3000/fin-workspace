//! The strategy drops its limit order before the venue has accepted it. The venue refuses the
//! cancel, since it doesn't know the order yet, and accepts a retry that comes after the ack.

use super::run_steps;
use crate::common::{Step, position, spy};
use oms::order::TerminationReason;
use tradeprim::Side;

#[test]
fn a_refused_cancel_is_retried_until_the_venue_has_the_order() {
    let (trace, oms, pf) = run_steps(
        &[
            ["100", "100", "100", "100"],
            ["100", "100", "100", "100"],
            ["100", "100", "100", "100"],
        ],
        &[Step::Place(Side::Buy, "95"), Step::Drop, Step::Wait],
    );

    assert_eq!(
        trace,
        [
            "01:00.000  candle 100/100/100/100, held 0, place Buy 1 @ 95",
            "01:00.000  send Limit 95 Buy 1",
            "02:00.000  candle 100/100/100/100, held 0, drop",
            "02:00.000  send cancel",
            "02:00.100  WARN cancel refused, retrying while the order is live",
            "02:00.100  cancel refused",
            "02:00.100  send cancel",
            "02:00.200  WARN cancel refused, retrying while the order is live",
            "02:00.200  cancel refused",
            "02:00.200  send cancel",
            // The venue accepts the order; a cancel is already on its way, so none is sent.
            "02:00.250  ack",
            // That cancel was sent before the ack: refused. The next one gets through.
            "02:00.300  WARN cancel refused, retrying while the order is live",
            "02:00.300  cancel refused",
            "02:00.300  send cancel",
            "02:00.400  cancelled",
            "03:00.000  candle 100/100/100/100, held 0, wait",
        ]
    );
    assert_eq!(pf.position(&spy()), &position(0));
    assert!(pf.fills().is_empty());
    assert_eq!(pf.orders().len(), 1);
    assert_eq!(pf.orders()[0].state().reason(), TerminationReason::Cancel);
    assert!(oms.is_empty(), "nothing left in flight");
}
