use chrono::DateTime;
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use mdata::{Candle, Instrumented, Tagged};
use oms::{
    OrderId,
    order::{New, Order, OrderBuilder},
};
use tradeprim::{Side, currency::Currency, price::Price, quantity::Quantity};

use super::SimQueue;
use crate::{
    event::{Event, EventSource, Kind, Request, Scheduler},
    executors::Executor,
    formats::frd::FrdCandle,
    market_data::FrdMdError,
};

type Record = Tagged<FrdCandle>;
type Stream = std::vec::IntoIter<Result<Record, FrdMdError>>;

/// Mock `Executor`, has two functions:
///     - Acks every order after `latency` nanos.
///     - Remembers every event it seen.
struct MockExec {
    latency: i64,
    seen: Vec<(i64, &'static str)>,
}

impl MockExec {
    fn new(latency: i64) -> Self {
        Self {
            latency,
            seen: Vec::new(),
        }
    }
}

impl Executor for MockExec {
    /// Just remember incoming event
    fn on_event<M: Candle + Instrumented>(
        &mut self,
        event: &Event<M>,
        _scheduler: &mut Scheduler<'_, M>,
    ) {
        self.seen.push((event.ts(), label(event)));
    }

    /// Ignore every request unless it's `SendOrder`.
    ///
    /// Acks such orders via scheduler.
    fn on_request<M>(
        &mut self,
        timestamp: i64,
        request: Request,
        scheduler: &mut Scheduler<'_, M>,
    ) {
        if let Request::SendOrder(order) = request {
            scheduler.push(timestamp + self.latency, Kind::Ack(order.order_id()));
        }
    }
}

fn label<R>(event: &Event<R>) -> &'static str {
    match event.kind() {
        Kind::MarketData(_) => "md",
        Kind::FeedError(_) => "feed error",
        Kind::Ack(_) => "ack",
        Kind::Fill(_) => "fill",
        Kind::Reject(_, _) => "reject",
        Kind::CancelResponse(_, _) => "cancel response",
        Kind::Expired(_, _) => "expired",
    }
}

fn spy() -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new("SPY", AssetClass::Equity).unwrap(),
        Asset::new("USD", AssetClass::Currency).unwrap(),
        Mic::arcx(),
        Currency::usd(),
    ))
}

fn bar(ts: i64) -> Result<Record, FrdMdError> {
    let px = Price::from_str_unchecked("1");
    Ok(Tagged::new(
        spy(),
        FrdCandle::new(DateTime::from_timestamp_nanos(ts), px, px, px, px, 1),
    ))
}

fn feed_error() -> Result<Record, FrdMdError> {
    Err(FrdMdError::Io(std::io::Error::other("boom")))
}

fn order() -> Order<New> {
    let qty = Quantity::from_str_unchecked("1").non_zero().unwrap();
    OrderBuilder::new(spy(), Side::Buy, qty)
        .verify()
        .unwrap()
        .build()
}

fn queue(md: Vec<Result<Record, FrdMdError>>, latency: i64) -> SimQueue<Stream, MockExec> {
    SimQueue::new(md.into_iter(), MockExec::new(latency))
}

/// Drains the queue, returning `(ts, label)` of every event.
fn drain(q: &mut SimQueue<Stream, MockExec>) -> Vec<(i64, &'static str)> {
    std::iter::from_fn(|| q.next_event())
        .map(|e| (e.ts(), label(&e)))
        .collect()
}

fn ack_id(event: Event<Record>) -> OrderId {
    match event.kind() {
        Kind::Ack(id) => *id,
        _ => panic!("expected an ack, got {event:?}"),
    }
}

#[test]
fn empty_stream_and_heap_end_immediately() {
    let mut q = queue(vec![], 0);
    assert!(q.next_event().is_none());
    assert_eq!(q.now(), 0);
}

#[test]
fn market_data_goes_out_in_order_and_moves_the_clock() {
    let mut q = queue(vec![bar(10), bar(20), bar(20), bar(30)], 0);

    assert_eq!(q.next_event().unwrap().ts(), 10);
    assert_eq!(q.now(), 10);
    assert_eq!(
        drain(&mut q),
        vec![(20, "md"), (20, "md"), (30, "md")],
        "equal timestamps are fine"
    );
    assert_eq!(q.now(), 30);
}

#[test]
fn a_scheduled_event_wins_a_tie_with_market_data() {
    let mut q = queue(vec![bar(10), bar(20)], 10);
    q.next_event().unwrap(); // md @ 10
    q.submit(Request::SendOrder(order())); // ack @ 20, same as the next bar

    assert_eq!(drain(&mut q), vec![(20, "ack"), (20, "md")]);
}

#[test]
fn market_data_before_a_scheduled_event_goes_first() {
    let mut q = queue(vec![bar(10), bar(15), bar(30)], 10);
    q.next_event().unwrap(); // md @ 10
    q.submit(Request::SendOrder(order())); // ack @ 20

    assert_eq!(drain(&mut q), vec![(15, "md"), (20, "ack"), (30, "md")]);
}

#[test]
fn scheduled_events_at_the_same_time_go_out_in_submission_order() {
    let mut q = queue(vec![bar(10)], 5);
    q.next_event().unwrap();
    // Many, not 2-3: `BinaryHeap` doesn't order equal keys, and with a handful of
    // orders the insertion order can come out by luck even without the `seq` tie-break.
    let orders: Vec<Order<New>> = (0..32).map(|_| order()).collect();
    for o in &orders {
        q.submit(Request::SendOrder(*o));
    }

    let acked: Vec<OrderId> = std::iter::from_fn(|| q.next_event()).map(ack_id).collect();
    let sent: Vec<OrderId> = orders.iter().map(|o| o.order_id()).collect();
    assert_eq!(acked, sent);
}

#[test]
fn scheduled_events_still_go_out_after_the_stream_ends() {
    let mut q = queue(vec![bar(10)], 100);
    q.next_event().unwrap();
    q.submit(Request::SendOrder(order()));

    assert_eq!(drain(&mut q), vec![(110, "ack")]);
    assert_eq!(q.now(), 110);
}

#[test]
fn a_feed_error_goes_out_at_the_current_time() {
    let mut q = queue(vec![bar(10), feed_error(), bar(20)], 0);

    assert_eq!(
        drain(&mut q),
        vec![(10, "md"), (10, "feed error"), (20, "md")]
    );
}

#[test]
fn a_scheduled_event_due_now_goes_before_a_feed_error() {
    let mut q = queue(vec![bar(10), feed_error()], 0);
    q.next_event().unwrap(); // md @ 10
    q.submit(Request::SendOrder(order())); // ack @ 10

    assert_eq!(drain(&mut q), vec![(10, "ack"), (10, "feed error")]);
}

#[test]
fn the_executor_is_shown_every_event_before_it_is_returned() {
    let mut q = queue(vec![bar(10), feed_error(), bar(20)], 5);

    // Already in `seen` the moment `next_event` returns it: shown before, not after.
    let step = |q: &mut SimQueue<Stream, MockExec>, expected: (i64, &'static str)| {
        let event = q.next_event().expect("one more event");
        assert_eq!((event.ts(), label(&event)), expected);
        assert_eq!(q.exec.seen.last(), Some(&expected));
    };

    step(&mut q, (10, "md"));
    q.submit(Request::SendOrder(order())); // ack @ 15
    step(&mut q, (10, "feed error"));
    step(&mut q, (15, "ack")); // a scheduled event, not just market data
    step(&mut q, (20, "md"));
    assert!(q.next_event().is_none());

    // Nothing skipped, nothing extra.
    assert_eq!(
        q.exec.seen,
        vec![(10, "md"), (10, "feed error"), (15, "ack"), (20, "md")]
    );
}

#[test]
fn submit_uses_the_current_time() {
    let mut q = queue(vec![bar(10), bar(50)], 7);
    q.next_event().unwrap(); // now = 10
    q.submit(Request::SendOrder(order()));

    assert_eq!(q.next_event().unwrap().ts(), 17);
}

#[test]
#[should_panic(expected = "market data at 10 is before now (20)")]
fn market_data_going_back_in_time_panics() {
    let mut q = queue(vec![bar(20), bar(10)], 0);
    drain(&mut q);
}
