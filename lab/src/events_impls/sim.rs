use std::{cmp::Reverse, collections::BinaryHeap, error::Error, iter::Peekable};

use mdata::{Candle, Instrumented, MarketData, Timestamped};

use crate::{
    event::{Event, EventSource, Kind, Request, Scheduled, Scheduler},
    executors::Executor,
};

/// Backtest event queue: one market-data stream merged with what a simulated
/// executor schedules (acks, fills, rejects, ...).
///
/// Works over any [`MarketData`] stream whose records are [`Candle`] +
/// [`Instrumented`], which is what the simulated executors fill against.
///
/// Ordering rules:
/// - the earliest timestamp goes first;
/// - on a tie, the scheduled event goes before the market data, so an ack or fill
///   reaches the strategy before the candle that comes at the same time;
/// - scheduled events with the same timestamp go out in the order they were scheduled;
/// - a feed error goes out at the current time, without moving the clock;
/// - time never goes backwards: a market-data record older than the current time panics.
///
/// Every event is shown to the executor before it is returned.
pub struct SimQueue<MD: MarketData, E> {
    now: i64,
    seq: u64,
    md: Peekable<MD>,
    heap: BinaryHeap<Reverse<Scheduled<MD::Record>>>,
    exec: E,
}

impl<MD: MarketData, E> SimQueue<MD, E> {
    /// Starts at time 0: the first event sets the clock.
    pub fn new(md: MD, exec: E) -> Self {
        Self {
            now: 0,
            seq: 0,
            md: md.peekable(),
            heap: BinaryHeap::new(),
            exec,
        }
    }

    /// Timestamp (nanos) of the last event handed out.
    pub fn now(&self) -> i64 {
        self.now
    }

    /// Sequence number the next scheduled event will get.
    pub fn seq(&self) -> u64 {
        self.seq
    }

    /// Events the executor has scheduled and that haven't gone out yet.
    pub fn heap(&self) -> &BinaryHeap<Reverse<Scheduled<MD::Record>>> {
        &self.heap
    }
}

fn nanos<T: Timestamped>(record: &T) -> i64 {
    record
        .timestamp()
        .timestamp_nanos_opt()
        .expect("market-data timestamp outside the i64-nanosecond range (years 1677..2262)")
}

impl<MD, E> EventSource for SimQueue<MD, E>
where
    MD: MarketData,
    MD::Record: Candle + Instrumented,
    MD::Error: Error + Send + 'static,
    E: Executor,
{
    type Record = MD::Record;

    fn next_event(&mut self) -> Option<Event<Self::Record>> {
        // peek at both: md and scheduled events
        let md_ts = match self.md.peek() {
            Some(Ok(record)) => Some(nanos(record)),
            Some(Err(_)) => Some(self.now),
            None => None,
        };
        let heap_ts = self.heap.peek().map(|next| next.0.event().ts());

        let scheduled_first = match (heap_ts, md_ts) {
            (None, None) => return None,
            (Some(heap_ts), Some(md_ts)) => heap_ts <= md_ts,
            (Some(_), None) => true,
            (None, Some(_)) => false,
        };

        // event extraction
        let event = if scheduled_first {
            let event = self.heap.pop().expect("just peeked").0.as_event();
            assert!(
                event.ts() >= self.now,
                "scheduled event at {} is before now ({}): {:?}",
                event.ts(),
                self.now,
                event
            );
            self.now = event.ts();
            event
        } else {
            match self.md.next().expect("just peeked") {
                Ok(record) => {
                    let ts = nanos(&record);
                    assert!(
                        ts >= self.now,
                        "market data at {} is before now ({}): {:?}",
                        ts,
                        self.now,
                        record
                    );
                    self.now = ts;
                    Event::new(ts, Kind::MarketData(record))
                }
                Err(err) => Event::new(self.now, Kind::FeedError(Box::new(err))),
            }
        };

        // limits what executor can do
        let mut scheduler = Scheduler::new(&mut self.heap, &mut self.seq);
        self.exec.on_event(&event, &mut scheduler);
        Some(event)
    }

    fn submit(&mut self, req: Request) {
        let mut scheduler = Scheduler::new(&mut self.heap, &mut self.seq);
        self.exec.on_request(self.now, req, &mut scheduler);
    }
}

#[cfg(test)]
mod tests;
