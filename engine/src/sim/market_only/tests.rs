//! Tests for invariants of a simplest market executor: [`MarketExecutor`]

use oms::order::OrderType;
use tradeprim::Side;

use super::MarketExecutor;
use crate::{
    event::{Kind, Request},
    sim::fixtures::{ACK, CANCEL, FILL, OHLC, REJECT, SEC, bar, events, order, px, run, send, spy},
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
            matches!(event.kind(), Kind::Ack(_))
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
