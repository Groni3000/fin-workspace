//! `telemetry::init` and the real `Oms` together: every order-lifecycle line lands in the
//! execution log, and nothing else does.
//!
//! The only test in this file: `init` sets the global subscriber, which a process can do once,
//! and each file in `tests/` is its own process.

use std::{fs, path::Path};

use engine::telemetry::{self, SimClock};
use foldhash::HashMap;
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use jiff::Timestamp;
use oms::{
    desired::Desired,
    fill::Fill,
    manager::Oms,
    order::{New, Order, OrderBuilder, OrderType},
    portfolio::Portfolio,
    protocol::{ExecEvent, RejectReason, Request, RequestSink},
    rms::NaiveRms,
};
use tradeprim::{
    Side,
    currency::Currency,
    position::{NonZeroQuantity, Position},
    price::Price,
    quantity::Quantity,
};

/// Keeps every request, so the test can name the orders the OMS created.
#[derive(Default)]
struct Sent(Vec<Request>);

impl RequestSink for Sent {
    fn submit(&mut self, req: Request) {
        self.0.push(req);
    }
}

impl Sent {
    fn order(&self, i: usize) -> Order<New> {
        match self.0[i] {
            Request::SendOrder(order) => order,
            ref other => panic!("request #{i} is not an order: {other:?}"),
        }
    }
}

fn spy() -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new("SPY", AssetClass::Equity).expect("valid asset"),
        Asset::new("USD", AssetClass::Currency).expect("valid asset"),
        Mic::arcx(),
        Currency::usd(),
    ))
}

fn qty(q: &str) -> NonZeroQuantity {
    Quantity::from_str_unchecked(q)
        .non_zero()
        .expect("non-zero quantity")
}

fn limit(q: &str, price: &str) -> Order<New> {
    OrderBuilder::new(spy(), Side::Buy, qty(q))
        .with_order_type(OrderType::Limit(Price::from_str_unchecked(price)))
        .verify()
        .expect("a valid order")
        .build()
}

fn fill(order: &Order<New>, q: &str) -> ExecEvent {
    ExecEvent::Fill(Fill::new(
        order.order_id(),
        Timestamp::UNIX_EPOCH,
        spy(),
        order.side(),
        qty(q),
        Price::from_str_unchecked("100"),
    ))
}

/// The one file in `dir` whose name starts with `prefix`.
fn read_log(dir: &Path, prefix: &str) -> String {
    let files: Vec<_> = fs::read_dir(dir)
        .expect("log dir exists")
        .map(|entry| entry.expect("readable entry").path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with(prefix))
        })
        .collect();
    assert_eq!(files.len(), 1, "{prefix}*: {files:?}");
    fs::read_to_string(&files[0]).expect("readable log")
}

#[test]
fn order_lifecycle_lines_go_to_the_exec_log_and_nothing_else_does() {
    let dir = std::env::temp_dir().join(format!("engine-telemetry-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    telemetry::init(SimClock::new(), &dir, "test").expect("init");

    tracing::warn!("not an order line");

    let (mut oms, mut pf, mut sent, rms) =
        (Oms::default(), Portfolio::new(), Sent::default(), NaiveRms);
    let mut desired = HashMap::from_iter([(spy(), Desired::new())]);
    let want = desired.get_mut(&spy()).expect("just inserted");
    want.set_desired_position(Position::Long(qty("2")));
    want.set_desired_orders(vec![limit("1", "99")]);

    // A limit and a market order go out and are acked; the market order fills in two parts.
    oms.reconcile(&desired, &pf, &rms, &mut sent);
    let (lmt, mkt) = (sent.order(0), sent.order(1));
    oms.on_exec(&ExecEvent::Ack(lmt.order_id()), &mut pf);
    oms.on_exec(&ExecEvent::Ack(mkt.order_id()), &mut pf);
    oms.on_exec(&fill(&mkt, "1"), &mut pf);
    oms.on_exec(&fill(&mkt, "1"), &mut pf);

    // The strategy drops the limit: it's cancelled.
    let want = desired.get_mut(&spy()).expect("still there");
    want.remove_order(lmt.order_id());
    oms.reconcile(&desired, &pf, &rms, &mut sent);
    oms.on_exec(&ExecEvent::CancelResponse(lmt.order_id(), true), &mut pf);

    // A new limit goes out and is rejected; then a fill nobody knows about.
    let want = desired.get_mut(&spy()).expect("still there");
    want.set_desired_orders(vec![limit("1", "98")]);
    oms.reconcile(&desired, &pf, &rms, &mut sent);
    let rejected = sent.order(3);
    oms.on_exec(
        &ExecEvent::Reject(rejected.order_id(), RejectReason::Venue("no".to_string())),
        &mut pf,
    );
    oms.on_exec(&fill(&limit("1", "97"), "1"), &mut pf);

    let exec: Vec<(String, String, String)> = read_log(&dir, "test.exec.")
        .lines()
        .map(|line| {
            let json: serde_json::Value = serde_json::from_str(line).expect("a JSON line");
            let text = |v: &serde_json::Value| v.as_str().expect("a string").to_string();
            (
                text(&json["target"]),
                text(&json["level"]),
                text(&json["fields"]["message"]),
            )
        })
        .collect();
    let expected: Vec<(String, String, String)> = [
        ("INFO", "send desired order"),
        ("INFO", "send market order"),
        ("INFO", "ack"),
        ("INFO", "ack"),
        ("INFO", "fill"),
        ("INFO", "fill"),
        ("INFO", "send cancel"),
        ("INFO", "cancelled"),
        ("INFO", "send desired order"),
        ("WARN", "reject"),
        ("INFO", "fill"),
        ("WARN", "fill for unknown order"),
    ]
    .into_iter()
    .map(|(level, message)| ("exec".to_string(), level.to_string(), message.to_string()))
    .collect();
    assert_eq!(exec, expected);

    let diag = read_log(&dir, "test.diag.");
    let lines: Vec<_> = diag.lines().collect();
    assert_eq!(lines.len(), 1, "{diag}");
    assert!(lines[0].ends_with("WARN not an order line"), "{diag}");

    let _ = fs::remove_dir_all(&dir);
}
