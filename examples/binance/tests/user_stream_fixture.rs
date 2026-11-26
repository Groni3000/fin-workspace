//! The user stream parser on a recorded demo round trip: a market buy of 0.0001 BTCUSDT, then a
//! market sell of the same, with fees taken from the received asset.

use binance_example::user_stream::{Update, parse};
use oms::protocol::ExecEvent;

const FIXTURE: &str = include_str!("fixtures/demo-user_stream-round_trip.jsonl");

#[test]
fn a_round_trip_reads_as_ack_fill_ack_fill() {
    let summary: Vec<String> = FIXTURE
        .lines()
        .map(|line| match parse(line).expect("parses") {
            Update::Exec(ExecEvent::Ack(id)) => format!("ack {id:?}"),
            Update::Fill { fill, fee } => format!(
                "fill {:?} {:?} {} @ {} at {}, fee {} {}",
                fill.order_id(),
                fill.side(),
                fill.quantity().qty(),
                fill.price(),
                fill.timestamp(),
                fee.amount,
                fee.asset
            ),
            Update::Other => "other".to_string(),
            other => panic!("unexpected {other:?}"),
        })
        .collect();
    assert_eq!(
        summary,
        [
            "ack OrderId(01a218b9-59f3-763a-8883-00e35b195ca4)",
            "fill OrderId(01a218b9-59f3-763a-8883-00e35b195ca4) Buy 0.0001 @ 60440.01 at 2026-11-26T16:38:50.23Z, fee 0.00000010 BTC",
            "other",
            "ack OrderId(01a218b9-5e50-7765-9ec9-1a203f5ab239)",
            "fill OrderId(01a218b9-5e50-7765-9ec9-1a203f5ab239) Sell 0.0001 @ 60440 at 2026-11-26T16:38:51.346Z, fee 0.00604400 USDT",
            "other",
        ]
    );
}
