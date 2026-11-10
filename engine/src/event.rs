use std::{cmp::Reverse, collections::BinaryHeap};

use oms::protocol::{ExecEvent, RequestSink};

#[derive(Debug)]
pub struct Event<R> {
    /// nanos
    ts: i64,
    kind: Kind<R>,
}

impl<R> Event<R> {
    pub fn new(ts: i64, kind: Kind<R>) -> Self {
        Self { ts, kind }
    }

    pub fn ts(&self) -> i64 {
        self.ts
    }

    pub fn kind(&self) -> &Kind<R> {
        &self.kind
    }

    /// Moves the kind out, dropping the timestamp.
    pub fn into_kind(self) -> Kind<R> {
        self.kind
    }
}

pub struct Scheduled<R> {
    seq: u64,
    event: Event<R>,
}

impl<R> Scheduled<R> {
    pub fn new(seq: u64, event: Event<R>) -> Self {
        Self { seq, event }
    }

    pub fn seq(&self) -> u64 {
        self.seq
    }

    pub fn event(&self) -> &Event<R> {
        &self.event
    }

    pub fn as_event(self) -> Event<R> {
        self.event
    }
}

impl<R> PartialEq for Scheduled<R> {
    fn eq(&self, other: &Self) -> bool {
        self.event.ts == other.event.ts && self.seq == other.seq
    }
}

impl<R> Eq for Scheduled<R> {}

impl<R> PartialOrd for Scheduled<R> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<R> Ord for Scheduled<R> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.event.ts, self.seq).cmp(&(other.event.ts, other.seq))
    }
}

/// Sink for Scheduled Events
pub struct Scheduler<'q, R> {
    heap: &'q mut BinaryHeap<Reverse<Scheduled<R>>>,
    seq: &'q mut u64,
}

impl<'q, R> Scheduler<'q, R> {
    pub fn new(heap: &'q mut BinaryHeap<Reverse<Scheduled<R>>>, seq: &'q mut u64) -> Self {
        Self { heap, seq }
    }

    pub fn push(&mut self, ts: i64, kind: Kind<R>) {
        let seq = *self.seq;
        *self.seq += 1;
        self.heap
            .push(Reverse(Scheduled::new(seq, Event::new(ts, kind))));
    }
}

/// Hands out events in time order and accepts requests.
pub trait EventSource: RequestSink {
    type Record;
    fn next_event(&mut self) -> Option<Event<Self::Record>>;
}

#[derive(Debug)]
pub enum Kind<R> {
    MarketData(R),
    /// An executor's report about an order.
    Exec(ExecEvent),
    FeedError(Box<dyn std::error::Error + Send>),
    // Timer(TimerKind),
    // Operator(Command),
}

#[cfg(test)]
mod tests;
