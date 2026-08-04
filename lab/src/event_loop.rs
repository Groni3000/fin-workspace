use std::{cmp::Reverse, collections::BinaryHeap};

use chrono::{DateTime, Utc};

use crate::{
    event::{Event, Scheduled},
    market_data::MarketData,
};

#[derive(Debug)]
pub struct EventLoop<M: MarketData> {
    now: i64,
    seq_next: u64,
    heap: BinaryHeap<Reverse<Scheduled<M>>>,
    md: M,
}

impl<M: MarketData> EventLoop<M> {
    /// Returns the current time as a `DateTime<Utc>` (nanos).
    #[inline]
    pub fn now(&self) -> DateTime<Utc> {
        DateTime::from_timestamp_nanos(self.now)
    }

    /// Returns the current time as a `DateTime<Utc>` (nanos).
    ///
    /// Same as `EventLoop.now()`.
    #[inline]
    pub fn timestmap(&self) -> DateTime<Utc> {
        self.now()
    }

    /// Returns the next sequence number. Used to numerate events and solve conflicts
    /// when multiple events have the same timestamp
    #[inline]
    pub fn seq_next(&self) -> u64 {
        self.seq_next
    }

    pub fn heap(&self) -> &BinaryHeap<Reverse<Scheduled<M>>> {
        &self.heap
    }

    pub fn md(&self) -> &M {
        &self.md
    }
}

impl<M: MarketData> Iterator for EventLoop<M> {
    type Item = Event<M>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}
