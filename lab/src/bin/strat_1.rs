use std::{
    collections::HashMap,
    path::Path,
    str::FromStr,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use chrono::Datelike;
use futchain::{FutChain, ListedTenors};
use instrid::instruments::{FuturesContract, Instrument};
use lab::{
    event::EventSource,
    events_impls::{frd::FrdEventQueue, kafka::KafkaEventQueue},
    formats::{
        custom::{CustomDatabentoAggregatedCandle, CustomDatabentoConsumerMd, KafkaSettings},
        merged_custom_kafka::MergedCandle,
    },
    market_data::{FrdFutChainMdReader, FrdMdError},
    oms::Oms,
    portfolio::Portfolio,
    rms::{HaltedRms, MaxPositionRms, NaiveRms, Rms},
    strats_impl::strat_1::{config::Config, strategy::Strategy},
    telemetry::{self, SimClock},
};
use tradeprim::{
    position::{NonZeroQuantity, Position},
    quantity::Quantity,
};

fn main() {
    let clock = SimClock::new();
    // `LOG_JSON=1` emits one JSON object per line, for the analysis script.
    match std::env::var("LOG_JSON").as_deref() {
        Ok("1") => telemetry::init_json(clock.clone()),
        _ => telemetry::init(clock.clone()),
    }

    let config = Config::default();
    let mut strategy = Strategy::new("Frd RB backtest".into(), config);
    let listing = ListedTenors::monthly();
    let init_futures_contract = match strategy.config().instrument() {
        Instrument::Futures(fut) => fut,
        _ => panic!("This strategy is for futures only!"),
    };
    match source_from_args() {
        Source::FrdFiles => {
            let md = init_files_md(&listing, init_futures_contract)
                .unwrap()
                .peekable();
            let mut pf = Portfolio::new();
            let mut oms = Oms::new(HashMap::default(), HashMap::default());
            let mut event_queue = FrdEventQueue::new(0, 0, md);
            let rms = rms_from_args();

            tracing::info!(strategy = strategy.id(), "backtest start");
            while let Some(event) = event_queue.next_event() {
                clock.set(event.ts());

                oms.on_event(&event, &mut pf);
                strategy.on_event(&event, &pf);

                oms.reconcile(strategy.desired(), &pf, &rms, &mut event_queue);
            }
            let final_positions = pf
                .positions()
                .iter()
                .filter(|(_i, p)| *p != &Position::Flat)
                .map(|(i, p)| format!("{i}: {p}"))
                .collect::<Vec<_>>()
                .join(", ");
            tracing::info!(
                fills = pf.fills().len(),
                positions = %final_positions,
                "backtest done"
            );
        }
        Source::KafkaReplay => {
            let shutdown = Arc::new(AtomicBool::new(false));
            let handler_flag = shutdown.clone();
            ctrlc::set_handler(move || handler_flag.store(true, Ordering::Relaxed))
                .expect("failed to set Ctrl-C handler");

            let md = init_kafka_md(shutdown, init_futures_contract, &listing).peekable();
            let mut pf = Portfolio::new();
            let mut oms = Oms::new(HashMap::default(), HashMap::default());
            let mut event_queue = KafkaEventQueue::new(0, 0, md);
            let rms = rms_from_args();

            let mut i = 0;
            while let Some(event) = event_queue.next_event() {
                clock.set(event.ts());
                if i == 0 {
                    tracing::info!(strategy = strategy.id(), "backtest start");
                }
                if i % 1000 == 0 {
                    tracing::info!("processed {} events", i);
                    tracing::info!("this event: {:?}", &event);
                }
                i += 1;

                oms.on_event(&event, &mut pf);
                strategy.on_event(&event, &pf);

                oms.reconcile(strategy.desired(), &pf, &rms, &mut event_queue);
            }
            let final_positions = pf
                .positions()
                .iter()
                .filter(|(_i, p)| *p != &Position::Flat)
                .map(|(i, p)| format!("{i}: {p}"))
                .collect::<Vec<_>>()
                .join(", ");
            tracing::info!(
                fills = pf.fills().len(),
                positions = %final_positions,
                "backtest done"
            );
        }
        Source::KafkaReplayMerged => {
            let shutdown = Arc::new(AtomicBool::new(false));
            let handler_flag = shutdown.clone();
            ctrlc::set_handler(move || handler_flag.store(true, Ordering::Relaxed))
                .expect("failed to set Ctrl-C handler");

            let md = init_kafka_merged_md(shutdown, init_futures_contract, &listing).peekable();
            let mut pf = Portfolio::new();
            let mut oms = Oms::new(HashMap::default(), HashMap::default());
            let mut event_queue = KafkaEventQueue::new(0, 0, md);
            let rms = rms_from_args();

            let mut i = 0;
            while let Some(event) = event_queue.next_event() {
                clock.set(event.ts());
                if i == 0 {
                    tracing::info!(strategy = strategy.id(), "backtest start");
                }
                if i % 1000 == 0 {
                    tracing::info!("processed {} events", i);
                    tracing::info!("this event: {:?}", &event);
                }
                i += 1;

                oms.on_event(&event, &mut pf);
                strategy.on_event(&event, &pf);

                oms.reconcile(strategy.desired(), &pf, &rms, &mut event_queue);
            }
            let final_positions = pf
                .positions()
                .iter()
                .filter(|(_i, p)| *p != &Position::Flat)
                .map(|(i, p)| format!("{i}: {p}"))
                .collect::<Vec<_>>()
                .join(", ");
            tracing::info!(
                fills = pf.fills().len(),
                positions = %final_positions,
                "backtest done"
            );
        }
    }
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
    let current_year = chrono::Utc::now().year() as u16;
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
    let current_year = chrono::Utc::now().year() as u16;
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
) -> Result<FrdFutChainMdReader<'a>, FrdMdError> {
    let dir = Path::new("lab/data/files/futures/frd");
    let chain = FutChain::new(instrument, listing).expect("Failed to create FutChain");
    let market_data = FrdFutChainMdReader::new(chain, dir.to_path_buf())?;

    Ok(market_data)
}
