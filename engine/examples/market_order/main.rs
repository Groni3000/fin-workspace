//! Market orders through the full pipeline of a backtest: enter, add, exit, go short, exit.
//! See `README.md`.
//!
//! Backtests and replays only. Nothing yet decides what to do about positions a simulator
//! opened while a live feed was behind the market, once the feed catches up.

use std::{fs, path::Path};

use chrono::{DateTime, Utc};
use engine::{
    event::{Event, Kind},
    event_loop::run,
    sim::{MarketExecutor, SimQueue},
    strategy::Traded,
    telemetry::{self, SimClock},
};
use foldhash::HashMap;
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use mdata::{Candle, RelevantPrice, Tagged, Timestamped};
use oms::{
    desired::Desired, manager::Oms, portfolio::Portfolio, protocol::ExecEvent, rms::NaiveRms,
};
use tradeprim::{currency::Currency, position::Position, price::Price, quantity::Quantity};

const SEC: i64 = 1_000_000_000;
const MS: i64 = 1_000_000;

/// Simulated latencies: about 50 ms for the strategy to decide, plus about 150 ms of network
/// round trip.
const ACK: i64 = 200 * MS;
const FILL: i64 = 200 * MS;
const CANCEL: i64 = 200 * MS;
const REJECT: i64 = 200 * MS;

/// One-minute bars, the first at 00:01, and the position (signed lots) the strategy wants
/// after seeing each one.
const BARS: [(&str, &str, i64); 11] = [
    // open, close, want
    ("100", "101", 1),  // enter long 1
    ("102", "103", 1),  // unchanged: nothing sent, the buy is still working
    ("103", "102", 1),  // unchanged: nothing sent, long 1 is held
    ("102", "104", 2),  // add 1
    ("105", "106", 2),  // unchanged
    ("106", "104", 0),  // exit: sell 2
    ("103", "102", 0),  // unchanged
    ("102", "100", -1), // go short 1
    ("99", "98", -1),   // unchanged
    ("98", "99", 0),    // exit: buy 1
    ("100", "100", 0),  // unchanged
];

fn main() {
    let spy = spy();
    let md: Vec<_> = BARS
        .iter()
        .zip(1..)
        .map(|((open, close, _), minute)| bar(spy, minute * 60, open, close))
        .collect();
    let exec = MarketExecutor::new(ACK as u64, FILL as u64, CANCEL as u64, REJECT as u64);
    let mut queue = SimQueue::new(md.into_iter(), exec);

    let clock = SimClock::new();
    // Order lifecycle goes to `market_order.exec.*.log`,
    // everything else to `market_order.diag.*.log`.
    let logs = std::env::temp_dir().join("engine-example-market_order");
    // Clear previuos runs results
    let _ = fs::remove_dir_all(&logs);
    telemetry::init(clock.clone(), &logs, "market_order").expect("logging can start");
    println!("logs in {}", logs.display());

    let mut strategy = Scripted::new(spy, BARS.iter().map(|(_, _, want)| *want).collect());
    let (_oms, pf) = run(
        &mut queue,
        &mut strategy,
        Oms::default(),
        Portfolio::new(),
        &NaiveRms,
        &clock,
    );
    println!("final position: {}", pf.position(&spy));

    // The OMS's side of the story: what it sent, and what came back.
    println!("\nexecution log:");
    let exec = exec_log(&logs);
    for line in &exec {
        println!("{line}");
    }

    // What the README promises. `cargo test` runs this example, so it can't drift.
    let min = |m: i64| m * 60 * SEC;
    let expected = [
        (min(1), "bar open=100 close=101, want 1"),
        (min(1) + ACK, "ack"),
        (min(2), "bar open=102 close=103, want 1"),
        (min(2) + FILL, "fill Buy 1 @ 102"),
        (min(3), "bar open=103 close=102, want 1"),
        (min(4), "bar open=102 close=104, want 2"),
        (min(4) + ACK, "ack"),
        (min(5), "bar open=105 close=106, want 2"),
        (min(5) + FILL, "fill Buy 1 @ 105"),
        (min(6), "bar open=106 close=104, want 0"),
        (min(6) + ACK, "ack"),
        (min(7), "bar open=103 close=102, want 0"),
        (min(7) + FILL, "fill Sell 2 @ 103"),
        (min(8), "bar open=102 close=100, want -1"),
        (min(8) + ACK, "ack"),
        (min(9), "bar open=99 close=98, want -1"),
        (min(9) + FILL, "fill Sell 1 @ 99"),
        (min(10), "bar open=98 close=99, want 0"),
        (min(10) + ACK, "ack"),
        (min(11), "bar open=100 close=100, want 0"),
        (min(11) + FILL, "fill Buy 1 @ 100"),
    ];
    let expected: Vec<(i64, String)> = expected
        .into_iter()
        .map(|(ts, what)| (ts, what.to_string()))
        .collect();
    assert_eq!(strategy.seen, expected);
    assert_eq!(pf.position(&spy), &Position::Flat);
    assert_eq!(pf.fills().len(), 5);

    // One order per change of the wanted position, and only the difference.
    let expected = [
        "1970-01-01 00:01:00 UTC  send market order Buy 1",
        "1970-01-01 00:01:00.200 UTC  ack Buy 1",
        "1970-01-01 00:02:00.200 UTC  fill Buy 1 @ 102",
        "1970-01-01 00:04:00 UTC  send market order Buy 1",
        "1970-01-01 00:04:00.200 UTC  ack Buy 1",
        "1970-01-01 00:05:00.200 UTC  fill Buy 1 @ 105",
        "1970-01-01 00:06:00 UTC  send market order Sell 2",
        "1970-01-01 00:06:00.200 UTC  ack Sell 2",
        "1970-01-01 00:07:00.200 UTC  fill Sell 2 @ 103",
        "1970-01-01 00:08:00 UTC  send market order Sell 1",
        "1970-01-01 00:08:00.200 UTC  ack Sell 1",
        "1970-01-01 00:09:00.200 UTC  fill Sell 1 @ 99",
        "1970-01-01 00:10:00 UTC  send market order Buy 1",
        "1970-01-01 00:10:00.200 UTC  ack Buy 1",
        "1970-01-01 00:11:00.200 UTC  fill Buy 1 @ 100",
    ];
    assert_eq!(exec, expected);
}

/// The execution log, one line per entry: time, message, side, quantity and price where the
/// entry has them. Each entry in the file is a JSON object.
fn exec_log(dir: &Path) -> Vec<String> {
    let file = fs::read_dir(dir)
        .expect("the log folder exists")
        .map(|entry| entry.expect("a readable entry").path())
        .find(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("market_order.exec."))
        })
        .expect("an execution log");
    fs::read_to_string(file)
        .expect("a readable log")
        .lines()
        .map(|line| {
            let entry: serde_json::Value = serde_json::from_str(line).expect("a JSON line");
            let field = |name: &str| entry["fields"][name].as_str().map(str::to_string);
            let mut out = format!(
                "{}  {}",
                entry["timestamp"].as_str().expect("a timestamp"),
                field("message").expect("a message")
            );
            for part in [field("side"), field("qty")].into_iter().flatten() {
                out.push(' ');
                out.push_str(&part);
            }
            if let Some(price) = field("price") {
                out.push_str(&format!(" @ {price}"));
            }
            out
        })
        .collect()
}

/// The whole strategy: after each bar, want the position the script says.
///
/// It never sends an order. It says what it wants to hold, and the OMS sends what closes the
/// gap between that and what is held or already working. When the wanted position doesn't
/// change, the OMS sends nothing.
struct Scripted {
    instrument: Instrument,
    /// The position wanted after each bar, in signed lots.
    script: Vec<i64>,
    bars_seen: usize,
    desired: HashMap<Instrument, Desired>,
    /// Every event the strategy saw, for the printout and the check in `main`.
    seen: Vec<(i64, String)>,
}

impl Scripted {
    fn new(instrument: Instrument, script: Vec<i64>) -> Self {
        Self {
            instrument,
            script,
            bars_seen: 0,
            desired: HashMap::default(),
            seen: Vec::new(),
        }
    }
}

impl Traded<Tagged<Bar>> for Scripted {
    fn on_event(&mut self, event: &Event<Tagged<Bar>>, _pf: &Portfolio) {
        let what = match event.kind() {
            Kind::MarketData(bar) => {
                let lots = self.script[self.bars_seen];
                self.bars_seen += 1;
                let mut want = Desired::new();
                want.set_desired_position(position(lots));
                self.desired.insert(self.instrument, want);
                format!("bar open={} close={}, want {lots}", bar.open(), bar.close())
            }
            Kind::Exec(ExecEvent::Ack(_)) => "ack".to_string(),
            Kind::Exec(ExecEvent::Fill(fill)) => format!(
                "fill {:?} {} @ {}",
                fill.side(),
                fill.quantity().qty(),
                fill.price()
            ),
            other => format!("{other:?}"),
        };
        println!("{}  {what}", DateTime::from_timestamp_nanos(event.ts()));
        self.seen.push((event.ts(), what));
    }

    fn desired(&self) -> &HashMap<Instrument, Desired> {
        &self.desired
    }
}

/// Signed lots as a position: positive is long, negative short.
fn position(lots: i64) -> Position {
    let qty = |n: i64| {
        Quantity::from_str_unchecked(&n.to_string())
            .non_zero()
            .expect("non-zero quantity")
    };

    match lots {
        0 => Position::Flat,
        n if n > 0 => Position::Long(qty(n)),
        n => Position::Short(qty(-n)),
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
