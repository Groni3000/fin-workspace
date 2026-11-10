//! Shared by the simulated executors' tests: a bar with its own open/high/low/close,
//! and a run through `SimQueue` that describes every event.

use std::convert::Infallible;

use chrono::{DateTime, Utc};
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use mdata::{Candle, RelevantPrice, Tagged, Timestamped};
use oms::order::{New, Order, OrderBuilder, OrderType};
use tradeprim::{Side, currency::Currency, price::Price, quantity::Quantity};

use super::SimQueue;
use crate::{
    event::{Event, EventSource, Kind, RejectReason, Request},
    executor::Executor,
};

pub const MS: i64 = 1_000_000;
pub const SEC: i64 = 1_000_000_000;

// Different latencies, so each timestamp shows which one was applied.
/// 1ms
pub const ACK: i64 = MS;
/// 2ms
pub const CANCEL: i64 = 2 * MS;
/// 3ms
pub const REJECT: i64 = 3 * MS;
/// 5ms
pub const FILL: i64 = 5 * MS;

#[derive(Debug)]
pub struct Bar {
    ts: DateTime<Utc>,
    open: Price,
    high: Price,
    low: Price,
    close: Price,
}

impl Timestamped for Bar {
    fn timestamp(&self) -> DateTime<Utc> {
        self.ts
    }
}

impl RelevantPrice for Bar {
    fn last_price(&self) -> Price {
        self.close
    }
}

impl Candle for Bar {
    fn open(&self) -> Price {
        self.open
    }
    fn high(&self) -> Price {
        self.high
    }
    fn low(&self) -> Price {
        self.low
    }
    fn close(&self) -> Price {
        self.close
    }
    fn volume(&self) -> u64 {
        1
    }
}

pub type Record = Tagged<Bar>;
pub type Stream = std::vec::IntoIter<Result<Record, Infallible>>;

/// A bar at `secs`, as `[open, high, low, close]`.
pub fn bar(
    instrument: Instrument,
    secs: i64,
    [o, h, l, c]: [&str; 4],
) -> Result<Record, Infallible> {
    Ok(Tagged::new(
        instrument,
        Bar {
            ts: DateTime::from_timestamp(secs, 0).expect("valid timestamp"),
            open: Price::from_str_unchecked(o),
            high: Price::from_str_unchecked(h),
            low: Price::from_str_unchecked(l),
            close: Price::from_str_unchecked(c),
        },
    ))
}

/// The bar most tests trade against: opens at 100, ranges 95..105.
pub const OHLC: [&str; 4] = ["100", "105", "95", "102"];

pub fn spy() -> Instrument {
    stock("SPY")
}

pub fn qqq() -> Instrument {
    stock("QQQ")
}

fn stock(symbol: &str) -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new(symbol, AssetClass::Equity).expect("valid asset"),
        Asset::new("USD", AssetClass::Currency).expect("valid asset"),
        Mic::arcx(),
        Currency::usd(),
    ))
}

/// One share, day order.
pub fn order(instrument: Instrument, side: Side, order_type: OrderType) -> Order<New> {
    let qty = Quantity::from_str_unchecked("1")
        .non_zero()
        .expect("non-zero quantity");
    OrderBuilder::new(instrument, side, qty)
        .with_order_type(order_type)
        .verify()
        .expect("a valid order")
        .build()
}

pub fn px(price: &str) -> Price {
    Price::from_str_unchecked(price)
}

/// Sends `start` at time 0, then drains the queue. After each event, whatever
/// `react` returns is sent too. Returns every event as `(ts, description)`, with
/// orders named by their index in `orders`: `#0`, `#1`, ...
pub fn run<E: Executor>(
    exec: E,
    bars: Vec<Result<Record, Infallible>>,
    orders: &[Order<New>],
    start: Vec<Request>,
    mut react: impl FnMut(&Event<Record>) -> Option<Request>,
) -> Vec<(i64, String)> {
    let mut queue = SimQueue::new(bars.into_iter() as Stream, exec);
    for request in start {
        queue.submit(request);
    }
    let mut seen = Vec::new();
    while let Some(event) = queue.next_event() {
        seen.push((event.ts(), describe(&event, orders)));
        if let Some(request) = react(&event) {
            queue.submit(request);
        }
    }
    seen
}

/// `run` with no reactions: every order is sent at time 0.
pub fn send<E: Executor>(
    exec: E,
    bars: Vec<Result<Record, Infallible>>,
    orders: &[Order<New>],
) -> Vec<(i64, String)> {
    let start = orders.iter().map(|o| Request::SendOrder(*o)).collect();
    run(exec, bars, orders, start, |_| None)
}

fn describe(event: &Event<Record>, orders: &[Order<New>]) -> String {
    let name = |id| match orders.iter().position(|o| o.order_id() == id) {
        Some(i) => format!("#{i}"),
        None => "unknown order".to_string(),
    };
    match event.kind() {
        Kind::MarketData(_) => "bar".to_string(),
        Kind::Ack(id) => format!("ack {}", name(*id)),
        Kind::Fill(fill) => format!(
            "fill {} {:?} {} @ {}",
            name(fill.order_id()),
            fill.side(),
            fill.quantity().qty(),
            fill.price()
        ),
        Kind::Reject(id, reason) => {
            let reason = match reason {
                RejectReason::UnsupportedOrderType(_) => "unsupported order type",
                RejectReason::DuplicateOrderId => "duplicate order id",
                RejectReason::Venue(text) => text,
            };
            format!("reject {} {reason}", name(*id))
        }
        Kind::CancelResponse(id, ok) => format!("cancel {} {ok}", name(*id)),
        other => format!("{other:?}"),
    }
}

/// Converts `[(ts, "...")]` into what `run` returns.
pub fn events<const N: usize>(expected: [(i64, &str); N]) -> Vec<(i64, String)> {
    expected
        .into_iter()
        .map(|(ts, what)| (ts, what.to_string()))
        .collect()
}
