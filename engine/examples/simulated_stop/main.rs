//! A natural continuation of `market_order`, focused on simulating a stop: enter long at
//! market, exit at market once a candle's low reaches the stop. See `README.md`.
//!
//! Backtests and replays only, like `market_order`.

use std::{fs, path::Path};

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
use jiff::Timestamp;
use mdata::{Candle, Ohlcv, Tagged};
use oms::{
    desired::Desired, manager::Oms, portfolio::Portfolio, protocol::ExecEvent, rms::NaiveRms,
};
use tradeprim::{
    Side,
    currency::Currency,
    position::{NonZeroQuantity, Position},
    price::Price,
    quantity::Quantity,
    volume::Volume,
};

const SEC: i64 = 1_000_000_000;
const MS: i64 = 1_000_000;

const ACK: i64 = 200 * MS;
const FILL: i64 = 200 * MS;
const CANCEL: i64 = 200 * MS;
const REJECT: i64 = 200 * MS;

/// How far below the entry fill the stop is.
const STOP: &str = "2";

/// One-minute candles, the first at 00:01: open, high, low, close.
const CANDLES: [[&str; 4]; 6] = [
    ["100", "101", "99", "100"],   // enter long 1
    ["101", "102", "100", "101"],  // filled at 101: stop at 99
    ["100", "101", "99.5", "100"], // close to the stop, not through it
    ["100", "100", "99", "99.5"],  // low touches the stop: exit
    ["98", "99", "97", "98"],      // filled at 98, below the stop
    ["98", "99", "97", "98"],      // flat: nothing sent
];

fn main() {
    let spy = spy();
    let md: Vec<_> = CANDLES
        .iter()
        .zip(1..)
        .map(|(ohlc, minute)| candle(spy, minute * 60, *ohlc))
        .collect();
    let exec = MarketExecutor::new(ACK as u64, FILL as u64, CANCEL as u64, REJECT as u64);
    let mut queue = SimQueue::new(md.into_iter(), exec);

    let clock = SimClock::new();
    let logs = std::env::temp_dir().join("engine-example-simulated_stop");
    let _ = fs::remove_dir_all(&logs);
    telemetry::init(clock.clone(), &logs, "simulated_stop").expect("logging can start");
    println!("logs in {}", logs.display());

    let mut strategy = StopOut::new(spy);
    let (_oms, pf) = run(
        &mut queue,
        &mut strategy,
        Oms::default(),
        Portfolio::new(),
        &NaiveRms,
        &clock,
    );
    println!("final position: {}", pf.position(&spy));

    println!("\nexecution log:");
    let exec = exec_log(&logs);
    for line in &exec {
        println!("{line}");
    }

    // What the README promises. `cargo test` runs this example, so it can't drift.
    let _time = |m: i64| m * 60 * SEC;
    let expected = [
        (_time(1), "candle 100/101/99/100, want 1"),
        (_time(1) + ACK, "ack"),
        (_time(2), "candle 101/102/100/101"),
        (_time(2) + FILL, "fill Buy 1 @ 101, stop at 99"),
        (_time(3), "candle 100/101/99.5/100"),
        (_time(4), "candle 100/100/99/99.5, stop hit, want 0"),
        (_time(4) + ACK, "ack"),
        (_time(5), "candle 98/99/97/98"),
        (_time(5) + FILL, "fill Sell 1 @ 98"),
        (_time(6), "candle 98/99/97/98"),
    ];
    let expected: Vec<(i64, String)> = expected
        .into_iter()
        .map(|(ts, what)| (ts, what.to_string()))
        .collect();
    assert_eq!(strategy.seen, expected);
    assert_eq!(pf.position(&spy), &Position::Flat);

    let expected = [
        "1970-01-01T00:01:00Z  send market order Buy 1",
        "1970-01-01T00:01:00.2Z  ack Buy 1",
        "1970-01-01T00:02:00.2Z  fill Buy 1 @ 101",
        "1970-01-01T00:04:00Z  send market order Sell 1",
        "1970-01-01T00:04:00.2Z  ack Sell 1",
        "1970-01-01T00:05:00.2Z  fill Sell 1 @ 98",
    ];
    assert_eq!(exec, expected);
}

/// Long 1 from the first candle; flat once a candle's low reaches the stop. One trade only.
struct StopOut {
    instrument: Instrument,
    desired: HashMap<Instrument, Desired>,
    /// Set by the entry fill, cleared when the stop is hit.
    stop: Option<Price>,
    seen: Vec<(i64, String)>,
}

impl StopOut {
    fn new(instrument: Instrument) -> Self {
        Self {
            instrument,
            desired: HashMap::default(),
            stop: None,
            seen: Vec::new(),
        }
    }

    fn want(&mut self, position: Position) {
        let mut want = Desired::new();
        want.set_desired_position(position);
        self.desired.insert(self.instrument, want);
    }
}

impl Traded<Tagged<Ohlcv>> for StopOut {
    fn on_event(&mut self, event: &Event<Tagged<Ohlcv>>, _pf: &Portfolio) {
        let what = match event.kind() {
            Kind::MarketData(candle) => {
                let mut what = format!(
                    "candle {}/{}/{}/{}",
                    candle.open(),
                    candle.high(),
                    candle.low(),
                    candle.close()
                );
                if self.desired.is_empty() {
                    self.want(Position::Long(lots("1")));
                    what.push_str(", want 1");
                } else if let Some(stop) = self.stop
                    && candle.low() <= stop
                {
                    self.stop = None;
                    self.want(Position::Flat);
                    what.push_str(", stop hit, want 0");
                }
                what
            }
            Kind::Exec(ExecEvent::Ack(_)) => "ack".to_string(),
            Kind::Exec(ExecEvent::Fill(fill)) => {
                let mut what = format!(
                    "fill {:?} {} @ {}",
                    fill.side(),
                    fill.quantity().qty(),
                    fill.price()
                );
                // Measured from the real fill, not from the candle the decision was made on.
                if fill.side() == Side::Buy {
                    let distance = Price::from_str_unchecked(STOP).value();
                    let stop = Price::new(fill.price().value() - distance).expect("a stop above 0");
                    self.stop = Some(stop);
                    what.push_str(&format!(", stop at {stop}"));
                }
                what
            }
            other => format!("{other:?}"),
        };
        println!(
            "{}  {what}",
            Timestamp::from_nanosecond(event.ts().into()).expect("i64 nanoseconds are in range")
        );
        self.seen.push((event.ts(), what));
    }

    fn desired(&self) -> &HashMap<Instrument, Desired> {
        &self.desired
    }
}

fn lots(n: &str) -> NonZeroQuantity {
    Quantity::from_str_unchecked(n)
        .non_zero()
        .expect("non-zero quantity")
}

/// The execution log, one line per entry: time, message, side, quantity and price.
fn exec_log(dir: &Path) -> Vec<String> {
    let file = fs::read_dir(dir)
        .expect("the log folder exists")
        .map(|entry| entry.expect("a readable entry").path())
        .find(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("simulated_stop.exec."))
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

fn candle(
    spy: Instrument,
    secs: i64,
    [o, h, l, c]: [&str; 4],
) -> Result<Tagged<Ohlcv>, std::io::Error> {
    let px = Price::from_str_unchecked;
    let ts = Timestamp::from_second(secs).expect("valid timestamp");
    Ok(Tagged::new(
        spy,
        Ohlcv::new(ts, px(o), px(h), px(l), px(c), Volume::ZERO),
    ))
}

fn spy() -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new("SPY", AssetClass::Equity).expect("valid asset"),
        Asset::new("USD", AssetClass::Currency).expect("valid asset"),
        Mic::arcx(),
        Currency::usd().into(),
    ))
}

#[cfg(test)]
mod tests {
    #[test]
    fn runs_as_the_readme_describes() {
        super::main();
    }
}
