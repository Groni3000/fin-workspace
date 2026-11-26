//! Runs the engine on live candles with a strategy that only watches:
//! `cargo run -p binance-example --bin watch -- <profile> <symbol>`.
//!
//! Prints each event at its time (a candle's open time) and how long after that it arrived. The
//! engine's logs, with the feed's gaps and reconnects, go to `examples/binance/logs/`. Runs until
//! Ctrl-C; panics once the feed gives up.

use std::path::Path;
use std::process::ExitCode;
use std::time::{SystemTime, UNIX_EPOCH};

use binance_example::feed::{self, Watchdog};
use binance_example::instruments;
use binance_example::live::LiveQueue;
use binance_example::profile::Profile;
use engine::event::{Event, Kind};
use engine::event_loop::run;
use engine::strategy::Traded;
use engine::telemetry::{self, SimClock};
use foldhash::HashMap;
use instrid::instruments::Instrument;
use jiff::Timestamp;
use mdata::ohlcv::Ohlcv;
use mdata::{Candle, HasVolume, Tagged};
use oms::desired::Desired;
use oms::manager::Oms;
use oms::portfolio::Portfolio;
use oms::rms::NaiveRms;

const PROFILES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/profiles.toml");
const LOGS: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/logs");

fn main() -> ExitCode {
    match start() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn start() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut args = std::env::args().skip(1);
    let usage = "usage: watch <profile> <symbol>";
    let name = args.next().ok_or(usage)?;
    let symbol = args.next().ok_or(usage)?.to_uppercase();
    if instruments::by_symbol(&symbol).is_none() {
        let listed: Vec<_> = instruments::all().iter().map(|l| l.symbol).collect();
        return Err(format!("{symbol} is not listed; listed: {}", listed.join(", ")).into());
    }
    let env = Profile::load(Path::new(PROFILES), &name)?.env;

    let clock = SimClock::new();
    telemetry::init(clock.clone(), LOGS, &format!("watch-{name}"))?;
    println!("{symbol} on {name} ({env:?}); logs in {LOGS}");

    let mut queue = LiveQueue::start(feed::streams(env)?, symbol, Watchdog::default())?;
    run(
        &mut queue,
        &mut Watcher::default(),
        Oms::default(),
        Portfolio::new(),
        &NaiveRms,
        &clock,
    );
    Ok(())
}

/// The wall clock, ns since the Unix epoch.
fn wall_now() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos() as i64)
}

/// Prints what it sees and never wants a position.
#[derive(Default)]
struct Watcher {
    desired: HashMap<Instrument, Desired>,
}

impl Traded<Tagged<Ohlcv>> for Watcher {
    fn on_event(&mut self, event: &Event<Tagged<Ohlcv>>, _pf: &Portfolio) {
        let at = Timestamp::from_nanosecond(event.ts().into())
            .expect("i64 nanoseconds are in range")
            .strftime("%H:%M:%S");
        let after = format!("{:.2} s later", (wall_now() - event.ts()) as f64 / 1e9);
        match event.kind() {
            Kind::MarketData(c) => println!(
                "{at}  candle  o {}  h {}  l {}  c {}  v {}  ({after})",
                c.open(),
                c.high(),
                c.low(),
                c.close(),
                c.volume()
            ),
            Kind::FeedError(e) => println!("{at}  feed error: {e}  ({after})"),
            Kind::Exec(e) => println!("{at}  {e:?}  ({after})"),
        }
    }

    fn desired(&self) -> &HashMap<Instrument, Desired> {
        &self.desired
    }
}
