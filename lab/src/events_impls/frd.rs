use std::{cmp::Reverse, collections::BinaryHeap, iter::Peekable};

use crate::{
    FrdCandle,
    event::{Event, EventSource, Kind},
    market_data::{FrdFutChainMdReader, FrdMdError},
};

type MdRecord = Result<FrdCandle, FrdMdError>;

pub struct FrdEventQueue<'a> {
    now: i64,
    seq: u64,
    md: Peekable<FrdFutChainMdReader<'a>>,
    heap: BinaryHeap<Reverse<Event<FrdCandle>>>,
}

impl<'a> FrdEventQueue<'a> {
    pub fn new(now: i64, seq: u64, md: Peekable<FrdFutChainMdReader<'a>>) -> Self {
        let heap = BinaryHeap::new();
        Self { now, seq, md, heap }
    }

    pub fn now(&self) -> i64 {
        self.now
    }

    pub fn seq(&self) -> u64 {
        self.seq
    }

    pub fn heap(&self) -> &BinaryHeap<Reverse<Event<FrdCandle>>> {
        &self.heap
    }

    fn unwrap_md_record(&mut self, record: MdRecord) -> Option<Event<FrdCandle>> {
        if record.is_err() {
            return Some(Event::new(
                self.now,
                self.take_seq(),
                Kind::FeedError(Box::new(record.unwrap_err())),
            ));
        }
        let record = record.unwrap();
        let ts = record
            .timestamp
            .timestamp_nanos_opt()
            .expect("Malformed timestmap DateTime<Utc> from MD.");
        assert!(ts >= self.now, "MD timestamp is before current time.");
        self.now = ts;

        Some(Event::new(
            self.now,
            self.take_seq(),
            Kind::MarketData(record),
        ))
    }

    fn unwrap_heap_event(&mut self, heap_event: Event<FrdCandle>) -> Option<Event<FrdCandle>> {
        let ts = heap_event.ts();
        assert!(
            ts >= self.now,
            "Heap event timestamp is before current time."
        );
        self.now = ts;
        Some(heap_event)
    }

    fn take_seq(&mut self) -> u64 {
        let s = self.seq;
        self.seq += 1;
        s
    }
}

impl<'a> EventSource for FrdEventQueue<'a> {
    type Record = FrdCandle;

    fn next_event(&mut self) -> Option<Event<Self::Record>> {
        let md_peek = self.md.peek();
        let heap_peek = self.heap.peek();

        match (heap_peek, md_peek) {
            (None, None) => None,
            (None, Some(_md_record)) => {
                let a = self.md.next().unwrap();
                self.unwrap_md_record(a)
            }
            (Some(_event), None) => {
                let a = self.heap.pop().unwrap().0;
                self.unwrap_heap_event(a)
            }
            (Some(event), Some(md_record)) => {
                match md_record {
                    Err(_err) => {
                        let a = self.md.next().unwrap();
                        self.unwrap_md_record(a)
                    }
                    Ok(candle) => {
                        let md_ts = candle
                            .timestamp
                            .timestamp_nanos_opt()
                            .expect("Malformed timestamp DateTime<Utc> from MD.");

                        // Unwrap what's first
                        match md_ts.cmp(&event.0.ts()) {
                            // unwrap md
                            std::cmp::Ordering::Less => {
                                let a = self.md.next().unwrap();
                                self.unwrap_md_record(a)
                            }
                            // unwrap heap
                            std::cmp::Ordering::Greater | std::cmp::Ordering::Equal => {
                                let a = self.heap.pop().unwrap().0;
                                self.unwrap_heap_event(a)
                            }
                        }
                    }
                }
            }
        }
    }

    fn submit(&mut self, req: crate::event::Request) {
        todo!()
    }
}
