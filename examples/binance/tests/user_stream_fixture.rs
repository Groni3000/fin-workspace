//! The user stream parser on recorded messages.

use binance_example::user_stream::{Update, parse};
use oms::protocol::ExecEvent;

/// A demo round trip: a market buy of 0.0001 BTCUSDT, then a market sell of the same, with fees
/// taken from the received asset.
const ROUND_TRIP: &str = include_str!("fixtures/demo-user_stream-round_trip.jsonl");
/// A testnet market sell of 0.01 BTCEUR that took two bid levels: one report per trade.
const PARTIAL_FILL: &str = include_str!("fixtures/testnet-user_stream-partial_fill.jsonl");

fn summary(recording: &str) -> Vec<String> {
    recording
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
        .collect()
}

#[test]
fn a_round_trip_reads_as_ack_fill_ack_fill() {
    assert_eq!(
        summary(ROUND_TRIP),
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

/// Each trade is its own `TRADE` report carrying that trade's quantity (`l`), not the order's
/// running total (`z`: 0.00055, then 0.01).
#[test]
fn a_partial_fill_is_one_fill_per_trade() {
    assert_eq!(
        summary(PARTIAL_FILL),
        [
            "ack OrderId(01a218d5-e90e-704f-82b3-d793d8befbaa)",
            "fill OrderId(01a218d5-e90e-704f-82b3-d793d8befbaa) Sell 0.00055 @ 55193.76 at 2026-11-26T17:10:02.035Z, fee 0.00000000 EUR",
            "fill OrderId(01a218d5-e90e-704f-82b3-d793d8befbaa) Sell 0.00945 @ 55188.24 at 2026-11-26T17:10:02.035Z, fee 0.00000000 EUR",
            "other",
        ]
    );
}
