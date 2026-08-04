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
    heap: BinaryHeap<Reverse<Event<MdRecord>>>,
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

    pub fn heap(&self) -> &BinaryHeap<Reverse<Event<MdRecord>>> {
        &self.heap
    }

    fn unwrap_md_record(&mut self, record: MdRecord) -> Option<Event<MdRecord>> {
        if record.is_err() {
            return Some(Event::new(self.now, self.seq, Kind::MarketData(record)));
        }
        let record = record.unwrap();
        let ts = record
            .timestamp
            .timestamp_nanos_opt()
            .expect("Malformed timestmap DateTime<Utc> from MD.");
        assert!(ts >= self.now, "MD timestamp is before current time.");
        self.now = ts;

        Some(Event::new(self.now, self.seq, Kind::MarketData(Ok(record))))
    }

    fn unwrap_heap_event(&mut self, heap_event: Event<MdRecord>) -> Option<Event<MdRecord>> {
        self.seq += 1;
        let ts = heap_event.ts();
        assert!(
            ts >= self.now,
            "Heap event timestamp is before current time."
        );
        self.now = ts;
        Some(heap_event)
    }
}

impl<'a> EventSource for FrdEventQueue<'a> {
    type Record = Result<FrdCandle, FrdMdError>;

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
                self.seq += 1;
                match md_record {
                    Err(_err) => {
                        return Some(Event::new(
                            self.now,
                            self.seq,
                            Kind::MarketData(self.md.next().unwrap()),
                        ));
                    }
                    Ok(candle) => {
                        let md_ts = candle
                            .timestamp
                            .timestamp_nanos_opt()
                            .expect("Malformed timestamp DateTime<Utc> from MD.");

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
