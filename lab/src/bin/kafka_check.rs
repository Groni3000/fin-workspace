//! Dirty check:
//! - connect to a Kafka broker
//! - subscribe to one topic
//! - and dump raw messages
//!
//! Uses the **sync** `BaseConsumer` (poll-based) on purpose: it maps 1:1 onto `next_record`.

use rdkafka::config::ClientConfig;
use rdkafka::consumer::{BaseConsumer, Consumer};
use rdkafka::message::Message;
use std::time::Duration;

// --- Connection
const BOOTSTRAP_SERVERS: &str = "192.168.217.126:9092";
// const TOPIC: &str = "md.db.GLBX.MDP3.RB.FUT.merged.ohlcv-1s";
// const TOPIC: &str = "md.db.GLBX.MDP3.GC.FUT.merged.ohlcv-1s";
const TOPIC: &str = "md.databento.GLBX.MDP3.ohlcv-1s";
// const TOPIC: &str = "md.databento.GLBX.MDP3.trades";
const GROUP_ID: &str = "dirty-check";
const AUTO_OFFSET_RESET: &str = "latest";
// ---

fn main() {
    let consumer: BaseConsumer = ClientConfig::new()
        .set("bootstrap.servers", BOOTSTRAP_SERVERS)
        .set("group.id", GROUP_ID)
        .set("auto.offset.reset", AUTO_OFFSET_RESET)
        // Dirty check: never commit offsets, so re-running always re-reads.
        .set("enable.auto.commit", "false")
        .create()
        .expect("failed to create consumer");

    // let md = consumer
    //     .fetch_metadata(Some(TOPIC), Duration::from_secs(10))
    //     .unwrap();

    // assigning
    // let mut tpl = TopicPartitionList::new();
    // for t in md.topics() {
    //     for p in t.partitions() {
    //         // Offset::End = only new msgs (like `latest`); Offset::Beginning = from start
    //         tpl.add_partition_offset(TOPIC, p.id(), Offset::Beginning)
    //             .unwrap();
    //     }
    // }
    // consumer.assign(&tpl).unwrap();

    // // subscribing
    consumer
        .subscribe(&[TOPIC])
        .expect("failed to subscribe to topic");

    println!("Consuming '{TOPIC}' from {BOOTSTRAP_SERVERS} (offset reset: {AUTO_OFFSET_RESET})");

    let mut count: u64 = 0;
    // let mut start = Instant::now();
    loop {
        match consumer.poll(Duration::from_millis(500)) {
            None => continue,
            Some(Ok(msg)) => {
                count += 1;

                // Just to look at payload
                let payload = match msg.payload_view::<str>() {
                    Some(Ok(s)) => s.to_owned(),
                    Some(Err(e)) => format!("<payload is not valid UTF-8: {e}>"),
                    None => "<empty payload>".to_owned(),
                };

                let key = msg
                    .key()
                    .map(|k| String::from_utf8_lossy(k).into_owned())
                    .unwrap_or_else(|| "<none>".to_owned());

                // Format:
                // {
                // "symbol": "CLZ6-CLM7", "dataset": "GLBX.MDP3",
                // "schema": "ohlcv-1s", "instrument_id": 182572,
                // "publisher_id": 1,
                // "ts_event": 1783000818000000000,
                // "time": "2026-07-02T14:00:18+00:00",
                // "src": "CL.FUT",
                // "open": 0.92, "high": 0.92, "low": 0.92, "close": 0.92, "volume": 34}

                // if count % 50_000 == 0 {
                //     let elapsed = start.elapsed();
                //     println!(
                //         "#{count} key={key} partition={} offset={} ts={:?}\n  {payload}\n  elapsed: {:?}\n",
                //         msg.partition(),
                //         msg.offset(),
                //         msg.timestamp(),
                //         elapsed,
                //     );
                //     start = Instant::now();
                // }
                println!(
                    "#{count} key={key} partition={} offset={} ts={:?}\n  {payload}\n",
                    msg.partition(),
                    msg.offset(),
                    msg.timestamp(),
                );
            }
            Some(Err(e)) => eprintln!("kafka error: {e}"),
        }
    }
}
