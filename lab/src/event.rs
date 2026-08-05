use oms::{
    OrderId,
    fill::Fill,
    order::{New, Order},
};

#[derive(Debug)]
pub struct Event<R> {
    /// nanos
    ts: i64,
    kind: Kind<R>,
}

// impl<R> PartialEq for Event<R> {
//     fn eq(&self, o: &Self) -> bool {
//         self.ts == o.ts && self.seq == o.seq
//     }
// }
// impl<R> Eq for Event<R> {}
// impl<R> Ord for Event<R> {
//     fn cmp(&self, o: &Self) -> std::cmp::Ordering {
//         (self.ts, self.seq).cmp(&(o.ts, o.seq))
//     }
// }
// impl<R> PartialOrd for Event<R> {
//     fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
//         Some(self.cmp(o))
//     }
// }

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
        (&self.event.ts, self.seq).partial_cmp(&(&other.event.ts, other.seq))
    }
}

impl<R> Ord for Scheduled<R> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.event.ts, self.seq).cmp(&(other.event.ts, other.seq))
    }
}

pub trait EventSource {
    type Record;
    fn next_event(&mut self) -> Option<Event<Self::Record>>;
    fn submit(&mut self, req: Request);
}

#[derive(Debug)]
pub enum Kind<R> {
    MarketData(R),
    FeedError(Box<dyn std::error::Error + Send>),
    Ack(OrderId),
    Fill(Fill),
    Reject(OrderId),
    CancelResponse(OrderId, bool),
    // Timer(TimerKind),
    // Operator(Command),
}

#[derive(Debug)]
pub enum Request {
    SendOrder(Order<New>),
    CancelOrder(OrderId),
    /// (Timer, fire at ts)
    // StartTimer(TimerKind, i64),
    // CancelTimer(TimerKind),
    Snapshot,
}
