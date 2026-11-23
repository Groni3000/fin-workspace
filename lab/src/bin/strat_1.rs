use std::{
    path::Path,
    str::FromStr,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
    time::Duration,
};

use engine::{
    event_loop::run,
    sim::{MarketExecutor, SimQueue},
    telemetry::{self, SimClock},
};
use foldhash::{HashMap, HashMapExt};
use futchain::{FutChain, ListedTenors};
use instrid::instruments::{FuturesContract, Instrument};
use lab::{
    formats::{
        custom::{CustomDatabentoAggregatedCandle, CustomDatabentoConsumerMd, KafkaSettings},
        merged_custom_kafka::MergedCandle,
    },
    strats_impl::strat_1::{config::Config, strategy::Strategy},
};
use mdata::formats::frd::{ChainReader, ReadError};
use oms::{
    manager::Oms,
    portfolio::Portfolio,
    rms::{HaltedRms, MaxPositionRms, NaiveRms, Rms},
};
use tradeprim::{
    position::{NonZeroQuantity, Position},
    quantity::Quantity,
};

fn main() {
    let clock = SimClock::new();
    // `lab/logs/strat_1.exec.<date>.log` (orders, JSON) and `lab/logs/strat_1.diag.<date>.log`.
    telemetry::init(clock.clone(), "lab/logs", "strat_1").expect("logging can start");

    let config = Config::default();
    let mut strategy = Strategy::new("Frd RB backtest".into(), config);
    let listing = ListedTenors::monthly();
    let init_futures_contract = match strategy.config().instrument() {
        Instrument::Futures(fut) => fut,
        _ => panic!("This strategy is for futures only!"),
    };
    match source_from_args() {
        Source::FrdFiles => {
            let md = init_files_md(&listing, init_futures_contract).unwrap();
            let pf = Portfolio::new();
            let oms = Oms::default();
            let mut event_queue = SimQueue::new(
                md,
                MarketExecutor::new(
                    Duration::from_millis(250).as_nanos() as u64,
                    Duration::from_secs(1).as_nanos() as u64,
                    Duration::from_millis(250).as_nanos() as u64,
                    Duration::from_millis(250).as_nanos() as u64,
                ),
            );
            let rms = rms_from_args();

            tracing::info!(strategy = strategy.id(), "backtest start");
            let (oms, pf) = run(&mut event_queue, &mut strategy, oms, pf, &rms, &clock);
            log_done(&oms, &pf);
        }
        Source::KafkaReplay => {
            let shutdown = Arc::new(AtomicBool::new(false));
            let handler_flag = shutdown.clone();
            ctrlc::set_handler(move || handler_flag.store(true, Ordering::Relaxed))
                .expect("failed to set Ctrl-C handler");

            let md = init_kafka_md(shutdown, init_futures_contract, &listing);
            let pf = Portfolio::new();
            let oms = Oms::default();
            let mut event_queue = SimQueue::new(
                md,
                MarketExecutor::new(
                    Duration::from_millis(250).as_nanos() as u64,
                    Duration::from_secs(1).as_nanos() as u64,
                    Duration::from_millis(250).as_nanos() as u64,
                    Duration::from_millis(250).as_nanos() as u64,
                ),
            );
            let rms = rms_from_args();

            tracing::info!(strategy = strategy.id(), "backtest start");
            let (oms, pf) = run(&mut event_queue, &mut strategy, oms, pf, &rms, &clock);
            log_done(&oms, &pf);
        }
        Source::KafkaReplayMerged => {
            let shutdown = Arc::new(AtomicBool::new(false));
            let handler_flag = shutdown.clone();
            ctrlc::set_handler(move || handler_flag.store(true, Ordering::Relaxed))
                .expect("failed to set Ctrl-C handler");

            let md = init_kafka_merged_md(shutdown, init_futures_contract, &listing);
            let pf = Portfolio::new();
            let oms = Oms::default();
            let mut event_queue = SimQueue::new(
                md,
                MarketExecutor::new(
                    Duration::from_millis(250).as_nanos() as u64,
                    Duration::from_secs(1).as_nanos() as u64,
                    Duration::from_millis(250).as_nanos() as u64,
                    Duration::from_millis(250).as_nanos() as u64,
                ),
            );
            let rms = rms_from_args();

            tracing::info!(strategy = strategy.id(), "backtest start");
            let (oms, pf) = run(&mut event_queue, &mut strategy, oms, pf, &rms, &clock);
            log_done(&oms, &pf);
        }
    }
}

/// The end-of-backtest summary. Open orders are listed too: a final position can be an exit that
/// never filled, not what the strategy wanted.
fn log_done(oms: &Oms, pf: &Portfolio) {
    let positions = pf
        .positions()
        .iter()
        .filter(|(_i, p)| *p != &Position::Flat)
        .map(|(i, p)| format!("{i}: {p}"))
        .collect::<Vec<_>>()
        .join(", ");
    let unacked = oms.unacked().values().map(|o| {
        format!(
            "{}: {:?} {} {} (unacked)",
            o.instrument(),
            o.side(),
            o.quantity().qty(),
            o.order_type()
        )
    });
    let working = oms.working().values().map(|o| {
        format!(
            "{}: {:?} {} of {} {} (working)",
            o.instrument(),
            o.side(),
            o.state().leaves(),
            o.quantity().qty(),
            o.order_type()
        )
    });
    let mut open_orders = unacked.chain(working).collect::<Vec<_>>();
    open_orders.sort();
    tracing::info!(
        fills = pf.fills().len(),
        positions = %positions,
        open_orders = open_orders.len(),
        orders = %open_orders.join(", "),
        "backtest done"
    );
}

enum Source {
    FrdFiles,
    KafkaReplay,
    KafkaReplayMerged,
}

impl FromStr for Source {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "frd" => Ok(Source::FrdFiles),
            "kafka" => Ok(Source::KafkaReplay),
            "kafka_merged" => Ok(Source::KafkaReplayMerged),
            _ => Err(format!("Invalid source: {}", s)),
        }
    }
}

/// `cargo run --bin strat_1 -- frd naive|max|halted`
fn rms_from_args() -> Box<dyn Rms> {
    match std::env::args().nth(2).unwrap_or_default().as_str() {
        "naive" => Box::new(NaiveRms),
        "halted" => Box::new(HaltedRms),
        _ => Box::new(MaxPositionRms::new(
            NonZeroQuantity::new(Quantity::from_str_unchecked("2")).unwrap(),
        )),
    }
}

fn source_from_args() -> Source {
    std::env::args()
        .nth(1)
        .unwrap_or(String::from("frd"))
        .parse()
        .unwrap()
}

fn init_kafka_md(
    shutdown: Arc<AtomicBool>,
    instrument: FuturesContract,
    listing: &ListedTenors,
) -> CustomDatabentoConsumerMd<CustomDatabentoAggregatedCandle> {
    let globex = |instr: &FuturesContract| {
        format!(
            "{}{}{}",
            instr.base().name().as_str(),
            instr.tenor().code(),
            instr.year() % 10
        )
    };
    // --- Connection
    const BOOTSTRAP_SERVERS: &str = "192.168.217.126:9092";
    const TOPIC: &str = "md.databento.GLBX.MDP3.ohlcv-1s";
    const GROUP_ID: &str = "dirty-check";
    const AUTO_OFFSET_RESET: &str = "earliest";
    let mut fchain = futchain::FutChain::new(instrument, listing).unwrap();
    let mut symbols = HashMap::new();
    let current_year = jiff::ZonedDateTime::now().year() as u16;
    for year in current_year - 1..=current_year + 2 {
        while fchain.contract().year() < year {
            fchain.advance();
        }
        while fchain.contract().year() == year {
            let contract = fchain.contract();
            let code = globex(contract);
            let instrument = Instrument::Futures(*contract);
            if let Some(prev) = symbols.insert(code.to_owned(), instrument) {
                panic!("globex code {code} collides: {prev} and {instrument}");
            }
            fchain.advance();
        }
    }
    // ---
    println!("Consuming '{TOPIC}' from {BOOTSTRAP_SERVERS} (offset reset: {AUTO_OFFSET_RESET})");
    CustomDatabentoConsumerMd::new(
        BOOTSTRAP_SERVERS,
        GROUP_ID,
        AUTO_OFFSET_RESET,
        false,
        TOPIC,
        shutdown,
        symbols,
        KafkaSettings::new(1048576, 500, 1_000_000, 1048576),
    )
}

fn init_kafka_merged_md(
    shutdown: Arc<AtomicBool>,
    instrument: FuturesContract,
    listing: &ListedTenors,
) -> CustomDatabentoConsumerMd<MergedCandle> {
    let globex = |instr: &FuturesContract| {
        format!(
            "{}{}{}",
            instr.base().name().as_str(),
            instr.tenor().code(),
            instr.year() % 10
        )
    };
    // --- Connection
    const BOOTSTRAP_SERVERS: &str = "192.168.217.126:9092";
    const TOPIC: &str = "md.db.GLBX.MDP3.RB.FUT.merged.ohlcv-1s";
    const GROUP_ID: &str = "dirty-check";
    const AUTO_OFFSET_RESET: &str = "earliest";
    let mut fchain = futchain::FutChain::new(instrument, listing).unwrap();
    let mut symbols = HashMap::new();
    let current_year = jiff::ZonedDateTime::now().year() as u16;
    for year in current_year - 1..=current_year + 2 {
        while fchain.contract().year() < year {
            fchain.advance();
        }
        while fchain.contract().year() == year {
            let contract = fchain.contract();
            let code = globex(contract);
            let instrument = Instrument::Futures(*contract);
            if let Some(prev) = symbols.insert(code.to_owned(), instrument) {
                panic!("globex code {code} collides: {prev} and {instrument}");
            }
            fchain.advance();
        }
    }
    // ---
    println!("Consuming '{TOPIC}' from {BOOTSTRAP_SERVERS} (offset reset: {AUTO_OFFSET_RESET})");
    CustomDatabentoConsumerMd::new(
        BOOTSTRAP_SERVERS,
        GROUP_ID,
        AUTO_OFFSET_RESET,
        false,
        TOPIC,
        shutdown,
        symbols,
        KafkaSettings::new(1048576, 50, 1_000_000, 1048576),
    )
}
fn init_files_md<'a>(
    listing: &'a ListedTenors,
    instrument: FuturesContract,
) -> Result<ChainReader<'a>, ReadError> {
    let dir = Path::new("lab/data/files/futures/frd");
    let chain = FutChain::new(instrument, listing).expect("Failed to create FutChain");
    let market_data = ChainReader::new(chain, dir.to_path_buf())?;

    Ok(market_data)
}
