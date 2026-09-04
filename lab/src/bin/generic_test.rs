use std::{
    path::Path,
    str::FromStr,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    },
};

use foldhash::HashMap;
use futchain::{FutChain, ListedTenors};
use instrid::{asset::Asset, instruments::FuturesContract, mic::Mic, tenor::Tenor};

use lab::{
    formats::custom::{CustomDatabentoAggregatedCandle, CustomDatabentoConsumerMd, KafkaSettings},
    market_data::{Candle, FrdFutChainMdReader, FrdMdError},
    process_md,
};
use tradeprim::currency::Currency;

enum Source {
    FrdFiles,
    KafkaLive,
}

impl FromStr for Source {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "frd" => Ok(Source::FrdFiles),
            "kafka" => Ok(Source::KafkaLive),
            _ => Err(format!("Invalid source: {}", s)),
        }
    }
}

fn main() {
    let (total_records, last_record): (u64, Option<Box<dyn Candle>>) = match source_from_args() {
        Source::FrdFiles => {
            let listing = ListedTenors::monthly();
            let (total_records, last_record) =
                process_md(&mut init_files_md(&listing).unwrap()).unwrap();
            (total_records, Some(Box::new(last_record.unwrap())))
        }
        Source::KafkaLive => {
            let shutdown = Arc::new(AtomicBool::new(false));
            let handler_flag = shutdown.clone();
            ctrlc::set_handler(move || handler_flag.store(true, Ordering::Relaxed))
                .expect("failed to set Ctrl-C handler");

            let (total_records, last_record) = process_md(&mut init_kafka_md(shutdown)).unwrap();
            (
                total_records,
                last_record.map(|r| Box::new(r) as Box<dyn Candle>),
            )
        }
    };

    println!("Total lines: {}", total_records);
    println!(
        "Last record: {:?}",
        last_record.map(|c| (c.timestamp(), c.close()))
    );
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
) -> CustomDatabentoConsumerMd<CustomDatabentoAggregatedCandle> {
    // --- Connection
    const BOOTSTRAP_SERVERS: &str = "192.168.217.126:9092";
    // const TOPIC: &str = "md.db.GLBX.MDP3.RB.FUT.merged.ohlcv-1s";
    // const TOPIC: &str = "md.db.GLBX.MDP3.GC.FUT.merged.ohlcv-1s";
    const TOPIC: &str = "md.databento.GLBX.MDP3.ohlcv-1s";
    // const TOPIC: &str = "md.databento.GLBX.MDP3.trades";
    const GROUP_ID: &str = "dirty-check";
    const AUTO_OFFSET_RESET: &str = "earliest";
    // ---
    println!("Consuming '{TOPIC}' from {BOOTSTRAP_SERVERS} (offset reset: {AUTO_OFFSET_RESET})");
    CustomDatabentoConsumerMd::new(
        BOOTSTRAP_SERVERS,
        GROUP_ID,
        AUTO_OFFSET_RESET,
        false,
        TOPIC,
        shutdown,
        // Will skip all messages
        HashMap::default(),
        KafkaSettings::default(),
    )
}

fn init_files_md<'a>(listing: &'a ListedTenors) -> Result<FrdFutChainMdReader<'a>, FrdMdError> {
    let dir = Path::new("lab/data/files/futures/frd");
    let instrument: FuturesContract = FuturesContract::new_unchecked(
        Asset::new("RB", instrid::asset::AssetClass::Commodity).expect("Failed to create Asset"),
        Asset::new("USD", instrid::asset::AssetClass::Currency).expect("Failed to create Asset"),
        Mic::xnym(),
        Currency::usd(),
        2025,
        Tenor::December,
        None,
    );
    let chain = FutChain::new(instrument, listing).expect("Failed to create FutChain");
    let market_data = FrdFutChainMdReader::new(chain, dir.to_path_buf())?;

    Ok(market_data)
}
