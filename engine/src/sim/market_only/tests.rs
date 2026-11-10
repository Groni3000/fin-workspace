//! Tests for invariants of a simplest market executor: [`MarketExecutor`]

use std::{cmp::Reverse, collections::BinaryHeap};

use oms::{
    order::OrderType,
    protocol::{ExecEvent, RejectReason, Request},
};
use tradeprim::Side;

use super::MarketExecutor;
use crate::{
    event::{Kind, Scheduler},
    sim::fixtures::{
        ACK, CANCEL, FILL, OHLC, REJECT, Record, SEC, bar, events, order, px, run, send, spy,
    },
};

/// Creates a simple market executor with fixed latencies.
fn executor() -> MarketExecutor {
    MarketExecutor::new(ACK as u64, FILL as u64, CANCEL as u64, REJECT as u64)
}

/// Simulated executor invariant only
#[test]
fn a_market_order_fills_at_the_open_of_the_first_bar_after_its_ack() {
    let orders = [order(spy(), Side::Sell, OrderType::Market)];
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
            (60 * SEC + FILL, "fill #0 Sell 1 @ 100"),
            (120 * SEC, "bar"),
        ])
    );
}

/// Simulated executor invariant only
#[test]
fn stop_and_limit_orders_are_rejected() {
    let orders = [
        order(spy(), Side::Buy, OrderType::Stop(px("104"))),
        order(spy(), Side::Buy, OrderType::Limit(px("96"))),
    ];

    let seen = send(executor(), vec![bar(spy(), 60, OHLC)], &orders);

    assert_eq!(
        seen,
        events([
            (REJECT, "reject #0 unsupported order type"),
            (REJECT, "reject #1 unsupported order type"),
            (60 * SEC, "bar"),
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

/// A venue reject for an order this simulator never saw (e.g. a live order) changes nothing,
/// and doesn't panic.
///
/// Simulated executor invariant only
#[test]
fn a_venue_reject_for_an_unknown_order_is_ignored() {
    let mut exec = executor();
    let mut heap = BinaryHeap::<Reverse<_>>::new();
    let mut seq = 0;
    let pending = order(spy(), Side::Buy, OrderType::Market);
    let unknown = order(spy(), Side::Buy, OrderType::Market);
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
    let order = order(spy(), Side::Buy, OrderType::Market);
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
    let order = order(spy(), Side::Buy, OrderType::Market);
    let id = order.order_id();
    exec.push::<Record>(order, 0, &mut Scheduler::new(&mut heap, &mut seq));

    exec.on_reject(&id, &RejectReason::DuplicateOrderId);

    let still_pending: Vec<_> = exec.pending_orders().keys().copied().collect();
    assert_eq!(still_pending, [id]);
}
