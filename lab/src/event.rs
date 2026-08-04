use oms::{
    OrderId,
    fill::Fill,
    order::{New, Order},
};

#[derive(Debug)]
pub struct Event<R> {
    /// nanos
    ts: i64,
    seq: u64,
    kind: Kind<R>,
}

impl<R> PartialEq for Event<R> {
    fn eq(&self, o: &Self) -> bool {
        self.ts == o.ts && self.seq == o.seq
    }
}
impl<R> Eq for Event<R> {}
impl<R> Ord for Event<R> {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        (self.ts, self.seq).cmp(&(o.ts, o.seq))
    }
}
impl<R> PartialOrd for Event<R> {
    fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(o))
    }
}

impl<R> Event<R> {
    pub fn new(ts: i64, seq: u64, kind: Kind<R>) -> Self {
        Self { ts, seq, kind }
    }

    pub fn ts(&self) -> i64 {
        self.ts
    }

    pub fn seq(&self) -> u64 {
        self.seq
    }

    pub fn kind(&self) -> &Kind<R> {
        &self.kind
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
