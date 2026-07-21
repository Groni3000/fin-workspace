//! Dirty check:
//! - connect to a Kafka broker
//! - subscribe to one topic
//! - and dump raw messages
//!
//! Uses the **sync** `BaseConsumer` (poll-based) on purpose: it maps 1:1 onto `next_record`.
use lab::formats::custom::CustomDatabentoConsumerMd;
use lab::process_md;

fn main() {
    let mut md = init_kafka_md();

    // Process either
    let (total_reads, record) = process_md(&mut md).unwrap();
    println!("total_reads: {}, record: {:#?}", total_reads, record);
}

fn init_kafka_md() -> CustomDatabentoConsumerMd {
    // --- Connection
    const BOOTSTRAP_SERVERS: &str = "192.168.217.126:9092";
    // const TOPIC: &str = "md.db.GLBX.MDP3.RB.FUT.merged.ohlcv-1s";
    // const TOPIC: &str = "md.db.GLBX.MDP3.GC.FUT.merged.ohlcv-1s";
    const TOPIC: &str = "md.databento.GLBX.MDP3.ohlcv-1s";
    // const TOPIC: &str = "md.databento.GLBX.MDP3.trades";
    const GROUP_ID: &str = "dirty-check";
    const AUTO_OFFSET_RESET: &str = "latest";
    // ---
    println!("Consuming '{TOPIC}' from {BOOTSTRAP_SERVERS} (offset reset: {AUTO_OFFSET_RESET})");
    CustomDatabentoConsumerMd::new(BOOTSTRAP_SERVERS, GROUP_ID, AUTO_OFFSET_RESET, false, TOPIC)
}
