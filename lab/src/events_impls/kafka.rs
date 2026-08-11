use std::{cmp::Reverse, collections::BinaryHeap, fmt::Debug, iter::Peekable};

use chrono::{DateTime, TimeDelta, Utc};
use serde::de::DeserializeOwned;

use crate::{
    event::{Event, EventSource, Kind, Request, Scheduled, Scheduler},
    executor::SingleInstrumentOnlyMarketExecutor,
    formats::{Tagged, custom::CustomDatabentoConsumerMd},
    market_data::{RelevantPrice, Symboled, Timestamped},
};

pub struct KafkaEventQueue<T>
where
    T: DeserializeOwned + Symboled,
{
    now: i64,
    seq: u64,
    md: Peekable<CustomDatabentoConsumerMd<T>>,
    heap: BinaryHeap<Reverse<Scheduled<Tagged<T>>>>,
    exec: SingleInstrumentOnlyMarketExecutor,
}

impl<T> KafkaEventQueue<T>
where
    T: DeserializeOwned + Symboled,
{
    pub fn new(now: i64, seq: u64, md: Peekable<CustomDatabentoConsumerMd<T>>) -> Self {
        let heap = BinaryHeap::new();
        Self {
            now,
            seq,
            md,
            heap,
            exec: SingleInstrumentOnlyMarketExecutor::new(250_000_000, 3_000_000_000),
        }
    }

    pub fn now(&self) -> i64 {
        self.now
    }

    pub fn seq(&self) -> u64 {
        self.seq
    }

    pub fn heap(&self) -> &BinaryHeap<Reverse<Scheduled<Tagged<T>>>> {
        &self.heap
    }
}

impl<T> EventSource for KafkaEventQueue<T>
where
    T: DeserializeOwned + Symboled + Timestamped + Debug + RelevantPrice,
{
    type Record = Tagged<T>;

    fn next_event(&mut self) -> Option<Event<Self::Record>> {
        let md_peek = self.md.peek();
        let heap_peek = self.heap.peek();
        let md_ts = match md_peek {
            Some(Ok(record)) => record
                .timestamp()
                .timestamp_nanos_opt()
                .expect("MD timestamp is before current time."),
            Some(Err(_e)) => self.now(),
            None => i64::MAX,
        };
        let heap_ts = match heap_peek {
            Some(event) => event.0.event().ts(),
            None => i64::MAX,
        };

        if self.heap.is_empty() && self.md.peek().is_none() {
            return None;
        }

        let event = match heap_ts.cmp(&md_ts) {
            std::cmp::Ordering::Less | std::cmp::Ordering::Equal => {
                let event = self.heap.pop().unwrap().0.as_event();
                assert!(
                    heap_ts >= self.now,
                    "heap_ts: {} is less than self.now: {}, event: {:?}",
                    heap_ts,
                    self.now,
                    event
                );
                self.now = heap_ts;
                Some(event)
            }
            std::cmp::Ordering::Greater => match self.md.next() {
                Some(Ok(record)) => {
                    assert!(
                        md_ts >= self.now,
                        "md_ts: {} is less than self.now: {}",
                        md_ts,
                        self.now
                    );
                    self.now = md_ts;
                    let event = Event::new(self.now, Kind::MarketData(record));
                    Some(event)
                }
                Some(Err(err)) => {
                    let event = Event::new(self.now, Kind::FeedError(Box::new(err)));
                    self.now = md_ts;
                    Some(event)
                }
                None => None,
            },
        };

        match event {
            Some(event) => {
                let mut scheduler = Scheduler::new(&mut self.heap, &mut self.seq);
                self.exec.on_event(&event, &mut scheduler);
                Some(event)
            }
            None => None,
        }
    }

    fn submit(&mut self, req: Request) {
        match req {
            Request::SendOrder(order) => {
                let mut scheduler = Scheduler::new(&mut self.heap, &mut self.seq);
                self.exec.push(order, self.now, &mut scheduler);
            }
            Request::CancelOrder(_order_id) => {}
            Request::Snapshot => {}
        }
    }
}

#[derive(Debug)]
pub struct DateTimeTrigger {
    fired: bool,
    start_datetime: DateTime<Utc>,
    end_datetime: DateTime<Utc>,
}

impl DateTimeTrigger {
    pub fn new(start_datetime: DateTime<Utc>, tolerance: TimeDelta) -> Self {
        debug_assert!(tolerance.num_nanoseconds() > Some(0));
        Self {
            fired: false,
            start_datetime,
            end_datetime: start_datetime + tolerance,
        }
    }

    pub fn check_nanos(&mut self, ts: i64) -> bool {
        if self.fired {
            return false;
        }
        let ts = DateTime::from_timestamp_nanos(ts);
        if ts >= self.start_datetime && ts <= self.end_datetime {
            self.fired = true;
            true
        } else {
            false
        }
    }
    pub fn check_dt(&mut self, ts: DateTime<Utc>) -> bool {
        if self.fired {
            return false;
        }
        if ts >= self.start_datetime && ts <= self.end_datetime {
            self.fired = true;
            true
        } else {
            false
        }
    }
}
