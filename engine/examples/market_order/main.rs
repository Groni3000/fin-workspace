//! A market order through a backtest. See `README.md`.

use chrono::{DateTime, Utc};
use engine::{
    event::{Event, EventSource, Kind},
    sim::{MarketExecutor, SimQueue},
};
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use mdata::{Candle, RelevantPrice, Tagged, Timestamped};
use oms::{
    order::{New, Order, OrderBuilder},
    protocol::{ExecEvent, Request, RequestSink},
};
use tradeprim::{Side, currency::Currency, price::Price, quantity::Quantity};

const SEC: i64 = 1_000_000_000;
const MS: i64 = 1_000_000;

/// Simulated latencies.
const ACK: i64 = MS;
const FILL: i64 = 5 * MS;
const CANCEL: i64 = MS;
const REJECT: i64 = MS;

fn main() {
    let spy = spy();
    let md = vec![bar(spy, 60, "100", "101"), bar(spy, 120, "102", "103")];
    let exec = MarketExecutor::new(ACK as u64, FILL as u64, CANCEL as u64, REJECT as u64);
    let mut queue = SimQueue::new(md.into_iter(), exec);

    // The whole "strategy": buy 1 share on the first bar.
    let order = market_buy(spy, "1");
    let mut sent = false;

    let mut seen = Vec::new();
    while let Some(event) = queue.next_event() {
        let what = describe(&event, &order);
        println!("{}  {what}", DateTime::from_timestamp_nanos(event.ts()));
        seen.push((event.ts(), what));

        if !sent && matches!(event.kind(), Kind::MarketData(_)) {
            queue.submit(Request::SendOrder(order));
            sent = true;
        }
    }

    // What the README promises. `cargo test` runs this example, so it can't drift.
    let expected = [
        (60 * SEC, "bar open=100 close=101"),
        (60 * SEC + ACK, "ack (our order)"),
        (120 * SEC, "bar open=102 close=103"),
        (120 * SEC + FILL, "fill Buy 1 @ 102 (our order)"),
    ];
    let expected: Vec<(i64, String)> = expected
        .into_iter()
        .map(|(ts, what)| (ts, what.to_string()))
        .collect();
    assert_eq!(seen, expected);
}

fn describe(event: &Event<Tagged<Bar>>, ours: &Order<New>) -> String {
    let whose = |id| {
        if id == ours.order_id() {
            "our order"
        } else {
            "someone else's order"
        }
    };
    match event.kind() {
        Kind::MarketData(bar) => format!("bar open={} close={}", bar.open(), bar.close()),
        Kind::Exec(ExecEvent::Ack(id)) => format!("ack ({})", whose(*id)),
        Kind::Exec(ExecEvent::Fill(fill)) => format!(
            "fill {:?} {} @ {} ({})",
            fill.side(),
            fill.quantity().qty(),
            fill.price(),
            whose(fill.order_id())
        ),
        other => format!("{other:?}"),
    }
}

/// A one-minute bar: all the queue and the executor need from market data.
#[derive(Debug)]
struct Bar {
    ts: DateTime<Utc>,
    open: Price,
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
        self.open.max(self.close)
    }
    fn low(&self) -> Price {
        self.open.min(self.close)
    }
    fn close(&self) -> Price {
        self.close
    }
    fn volume(&self) -> u64 {
        0
    }
}

/// A market-data stream is just an iterator of `Result`s. This one never fails.
fn bar(spy: Instrument, secs: i64, open: &str, close: &str) -> Result<Tagged<Bar>, std::io::Error> {
    let bar = Bar {
        ts: DateTime::from_timestamp(secs, 0).expect("valid timestamp"),
        open: Price::from_str_unchecked(open),
        close: Price::from_str_unchecked(close),
    };
    Ok(Tagged::new(spy, bar))
}

fn market_buy(instrument: Instrument, qty: &str) -> Order<New> {
    let qty = Quantity::from_str_unchecked(qty)
        .non_zero()
        .expect("non-zero quantity");
    OrderBuilder::new(instrument, Side::Buy, qty)
        .verify()
        .expect("a market order needs nothing else")
        .build()
}

fn spy() -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new("SPY", AssetClass::Equity).expect("valid asset"),
        Asset::new("USD", AssetClass::Currency).expect("valid asset"),
        Mic::arcx(),
        Currency::usd(),
    ))
}

#[cfg(test)]
mod tests {
    #[test]
    fn runs_as_the_readme_describes() {
        super::main();
    }
}
