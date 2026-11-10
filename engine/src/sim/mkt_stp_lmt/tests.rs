//! Tests for invariants of a market, stop and limit executor: [`MarketStopLimitExecutor`]

use std::{cmp::Reverse, collections::BinaryHeap};

use oms::{
    order::OrderType,
    protocol::{ExecEvent, RejectReason, Request},
};
use tradeprim::Side;

use super::MarketStopLimitExecutor;
use crate::{
    event::{Kind, Scheduler},
    sim::fixtures::{
        ACK, CANCEL, FILL, OHLC, REJECT, Record, SEC, bar, events, order, px, qqq, run, send, spy,
    },
};

/// Creates a market, stop and limit executor with fixed latencies.
fn executor() -> MarketStopLimitExecutor {
    MarketStopLimitExecutor::new(ACK as u64, FILL as u64, CANCEL as u64, REJECT as u64)
}

/// Sends one order, then shows it the `OHLC` bar at 60s.
/// Returns the fill price, or `None` if it didn't fill.
fn fill_price(side: Side, order_type: OrderType) -> Option<String> {
    let orders = [order(spy(), side, order_type)];
    let seen = send(executor(), vec![bar(spy(), 60, OHLC)], &orders);
    match &seen[..] {
        [(ACK, ack), (bar_ts, _)] => {
            assert_eq!((ack.as_str(), *bar_ts), ("ack #0", 60 * SEC));
            None
        }
        [(ACK, ack), (_, _), (fill_ts, fill)] => {
            assert_eq!((ack.as_str(), *fill_ts), ("ack #0", 60 * SEC + FILL));
            let price = fill
                .strip_prefix(&format!("fill #0 {side:?} 1 @ "))
                .unwrap_or_else(|| panic!("not a fill of #0: {fill}"));
            Some(price.to_string())
        }
        other => panic!("unexpected events: {other:?}"),
    }
}

fn stop(price: &str) -> OrderType {
    OrderType::Stop(px(price))
}

fn limit(price: &str) -> OrderType {
    OrderType::Limit(px(price))
}

fn some(price: &str) -> Option<String> {
    Some(price.to_string())
}

/// Simulated executor invariant only
#[test]
fn a_market_order_fills_at_the_open_of_the_first_bar_after_its_ack() {
    let orders = [order(spy(), Side::Buy, OrderType::Market)];
    let bars = vec![
        bar(spy(), 60, OHLC),
        bar(spy(), 120, ["110", "115", "105", "112"]),
    ];

    let seen = send(executor(), bars, &orders);

    assert_eq!(
        seen,
        events([
            (ACK, "ack #0"),
            (60 * SEC, "bar"),
            (60 * SEC + FILL, "fill #0 Buy 1 @ 100"),
            (120 * SEC, "bar"),
        ])
    );
}

/// The bar opens at 100 and ranges 95..105.
///
/// Simulated executor invariant only
#[test]
fn a_buy_stop_fills_once_the_high_reaches_it() {
    assert_eq!(
        fill_price(Side::Buy, stop("104")),
        some("104"),
        "inside the bar"
    );
    assert_eq!(
        fill_price(Side::Buy, stop("105")),
        some("105"),
        "at the high"
    );
    assert_eq!(fill_price(Side::Buy, stop("106")), None, "above the high");
    assert_eq!(
        fill_price(Side::Buy, stop("98")),
        some("100"),
        "gapped through: the open, worse"
    );
}

/// Simulated executor invariant only
#[test]
fn a_sell_stop_fills_once_the_low_reaches_it() {
    assert_eq!(
        fill_price(Side::Sell, stop("96")),
        some("96"),
        "inside the bar"
    );
    assert_eq!(fill_price(Side::Sell, stop("95")), some("95"), "at the low");
    assert_eq!(fill_price(Side::Sell, stop("94")), None, "below the low");
    assert_eq!(
        fill_price(Side::Sell, stop("102")),
        some("100"),
        "gapped through: the open, worse"
    );
}

/// Simulated executor invariant only
#[test]
fn a_buy_limit_fills_once_the_low_reaches_it() {
    assert_eq!(
        fill_price(Side::Buy, limit("96")),
        some("96"),
        "inside the bar"
    );
    assert_eq!(fill_price(Side::Buy, limit("95")), some("95"), "at the low");
    assert_eq!(fill_price(Side::Buy, limit("94")), None, "below the low");
    assert_eq!(
        fill_price(Side::Buy, limit("103")),
        some("100"),
        "opened below it: the open, better"
    );
}

/// Simulated executor invariant only
#[test]
fn a_sell_limit_fills_once_the_high_reaches_it() {
    assert_eq!(
        fill_price(Side::Sell, limit("104")),
        some("104"),
        "inside the bar"
    );
    assert_eq!(
        fill_price(Side::Sell, limit("105")),
        some("105"),
        "at the high"
    );
    assert_eq!(fill_price(Side::Sell, limit("106")), None, "above the high");
    assert_eq!(
        fill_price(Side::Sell, limit("98")),
        some("100"),
        "opened above it: the open, better"
    );
}

/// Both real and simulated must hold this invariant
#[test]
fn an_order_that_did_not_trigger_keeps_working_until_a_later_bar_does() {
    let orders = [order(spy(), Side::Buy, stop("106"))];
    let bars = vec![
        bar(spy(), 60, OHLC),
        bar(spy(), 120, ["103", "107", "102", "106"]),
    ];

    let seen = send(executor(), bars, &orders);

    assert_eq!(
        seen,
        events([
            (ACK, "ack #0"),
            (60 * SEC, "bar"),
            (120 * SEC, "bar"),
            (120 * SEC + FILL, "fill #0 Buy 1 @ 106"),
        ])
    );
}

/// Simulated executor invariant only
#[test]
fn only_orders_for_the_bars_instrument_fill() {
    let orders = [
        order(spy(), Side::Buy, OrderType::Market),
        order(qqq(), Side::Buy, OrderType::Market),
    ];

    let seen = send(executor(), vec![bar(spy(), 60, OHLC)], &orders);

    assert_eq!(
        seen,
        events([
            (ACK, "ack #0"),
            (ACK, "ack #1"),
            (60 * SEC, "bar"),
            (60 * SEC + FILL, "fill #0 Buy 1 @ 100"),
        ])
    );
}

/// Simulated executor invariant only
#[test]
fn a_stop_limit_order_is_rejected() {
    let orders = [order(
        spy(),
        Side::Buy,
        OrderType::StopLimit(px("104"), px("105")),
    )];

    let seen = send(executor(), vec![bar(spy(), 60, OHLC)], &orders);

    assert_eq!(
        seen,
        events([
            (REJECT, "reject #0 unsupported order type"),
            (60 * SEC, "bar")
        ])
    );
}

/// Both real and simulated must hold this invariant
#[test]
fn a_duplicate_of_a_pending_order_is_rejected() {
    let orders = [order(spy(), Side::Buy, OrderType::Market)];
    let start = vec![Request::SendOrder(orders[0]), Request::SendOrder(orders[0])];

    let seen = run(
        executor(),
        vec![bar(spy(), 60, OHLC)],
        &orders,
        start,
        |_| None,
    );

    assert_eq!(
        seen,
        events([
            (ACK, "ack #0"),
            (REJECT, "reject #0 duplicate order id"),
            (60 * SEC, "bar"),
            (60 * SEC + FILL, "fill #0 Buy 1 @ 100"),
        ])
    );
}

/// Both real and simulated must hold this invariant
#[test]
fn a_cancelled_working_unfilled_order_does_not_fill() {
    let orders = [order(spy(), Side::Buy, OrderType::Market)];
    let start = vec![Request::SendOrder(orders[0])];
    let seen = run(
        executor(),
        vec![bar(spy(), 60, OHLC)],
        &orders,
        start,
        |event| {
            // Right after the ack: the order works, and no bar has come yet.
            matches!(event.kind(), Kind::Exec(ExecEvent::Ack(_)))
                .then(|| Request::CancelOrder(spy(), orders[0].order_id()))
        },
    );

    assert_eq!(
        seen,
        events([
            (ACK, "ack #0"),
            (ACK + CANCEL, "cancel #0 true"),
            (60 * SEC, "bar"),
        ])
    );
}

/// Both real and simulated must hold this invariant
#[test]
fn a_cancel_before_the_ack_still_lets_the_ack_out_but_the_order_never_fills() {
    let orders = [order(spy(), Side::Buy, OrderType::Market)];
    let start = vec![
        Request::SendOrder(orders[0]),
        Request::CancelOrder(spy(), orders[0].order_id()),
    ];

    let seen = run(
        executor(),
        vec![bar(spy(), 60, OHLC)],
        &orders,
        start,
        |_| None,
    );

    assert_eq!(
        seen,
        events([
            (ACK, "ack #0"),
            (CANCEL, "cancel #0 true"),
            (60 * SEC, "bar"),
        ])
    );
}

/// Both real and simulated must hold this invariant
#[test]
fn a_cancel_after_the_fill_was_decided_is_too_late() {
    let orders = [order(spy(), Side::Buy, OrderType::Market)];
    let start = vec![Request::SendOrder(orders[0])];

    let seen = run(
        executor(),
        vec![bar(spy(), 60, OHLC)],
        &orders,
        start,
        |event| {
            // On the bar, which has already scheduled the fill.
            (event.ts() == 60 * SEC).then(|| Request::CancelOrder(spy(), orders[0].order_id()))
        },
    );

    assert_eq!(
        seen,
        events([
            (ACK, "ack #0"),
            (60 * SEC, "bar"),
            (60 * SEC + CANCEL, "cancel #0 false"),
            (60 * SEC + FILL, "fill #0 Buy 1 @ 100"),
        ])
    );
}

/// Simulated executor invariant only
#[test]
fn an_order_is_pending_until_its_ack_then_working() {
    let mut exec = executor();
    let mut heap = BinaryHeap::<Reverse<_>>::new();
    let mut seq = 0;
    let order = order(spy(), Side::Buy, stop("104"));
    let id = order.order_id();

    exec.push::<Record>(order, 0, &mut Scheduler::new(&mut heap, &mut seq));
    let pending: Vec<_> = exec.pending_orders().keys().copied().collect();
    assert_eq!(pending, [id]);
    assert!(exec.working_orders().is_empty());

    exec.on_ack(&id);
    assert!(exec.pending_orders().is_empty());
    let working: Vec<_> = exec.working_orders()[&spy()]
        .iter()
        .map(|o| o.order_id())
        .collect();
    assert_eq!(working, [id]);
}

/// A venue reject for an order this simulator never saw (e.g. a live order) changes nothing,
/// and doesn't panic.
///
/// Simulated executor invariant only
#[test]
fn a_venue_reject_for_an_unknown_order_is_ignored() {
    let mut exec = executor();
    let mut heap = BinaryHeap::<Reverse<_>>::new();
    let mut seq = 0;
    let pending = order(spy(), Side::Buy, stop("104"));
    let unknown = order(spy(), Side::Buy, stop("104"));
    exec.push::<Record>(pending, 0, &mut Scheduler::new(&mut heap, &mut seq));

    exec.on_reject(
        &unknown.order_id(),
        &RejectReason::Venue("rejected".to_string()),
    );

    let still_pending: Vec<_> = exec.pending_orders().keys().copied().collect();
    assert_eq!(still_pending, [pending.order_id()]);
    assert!(exec.working_orders().is_empty());
}

/// A venue reject of a pending order removes it, so its ack doesn't make it work.
///
/// Simulated executor invariant only
#[test]
fn a_venue_rejected_pending_order_never_works() {
    let mut exec = executor();
    let mut heap = BinaryHeap::<Reverse<_>>::new();
    let mut seq = 0;
    let order = order(spy(), Side::Buy, stop("104"));
    let id = order.order_id();
    exec.push::<Record>(order, 0, &mut Scheduler::new(&mut heap, &mut seq));

    exec.on_reject(&id, &RejectReason::Venue("rejected".to_string()));
    exec.on_ack(&id);

    assert!(exec.pending_orders().is_empty());
    assert!(exec.working_orders().is_empty());
}

/// The reject of a duplicate names the original order's id: the original stays pending.
/// (In `a_duplicate_of_a_pending_order_is_rejected` the original is acked before the reject
/// arrives, so it doesn't cover this.)
///
/// Simulated executor invariant only
#[test]
fn a_duplicate_reject_keeps_the_original_pending() {
    let mut exec = executor();
    let mut heap = BinaryHeap::<Reverse<_>>::new();
    let mut seq = 0;
    let order = order(spy(), Side::Buy, stop("104"));
    let id = order.order_id();
    exec.push::<Record>(order, 0, &mut Scheduler::new(&mut heap, &mut seq));

    exec.on_reject(&id, &RejectReason::DuplicateOrderId);

    let still_pending: Vec<_> = exec.pending_orders().keys().copied().collect();
    assert_eq!(still_pending, [id]);
}
