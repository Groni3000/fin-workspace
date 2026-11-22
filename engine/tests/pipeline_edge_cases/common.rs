use std::{cell::RefCell, rc::Rc};

use chrono::DateTime;
use engine::{
    event::{Event, EventSource, Kind},
    event_loop::run,
    strategy::Traded,
    telemetry::SimClock,
};
use foldhash::HashMap;
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use mdata::{Candle, Ohlcv, Tagged};
use oms::{
    desired::Desired,
    manager::Oms,
    portfolio::Portfolio,
    protocol::{ExecEvent, Request, RequestSink},
    rms::Rms,
};
use tradeprim::{currency::Currency, position::Position, quantity::Quantity};

pub type Record = Tagged<Ohlcv>;
/// Ideally, `Trace = Vec<String>`, but two writers fill it:
/// the queue (requests) and the strategy (events).
/// `run` holds both mutably at the same time.
///
/// So we share (`Rc`), and the borrow rules are checked at runtime (`RefCell`).
type Trace = Rc<RefCell<Vec<String>>>;

/// Runs the scripted strategy over `queue` (with some executor).
///
/// Returns its trace, the OMS and the final portfolio.
pub fn run_scripted<Q, R>(queue: Q, wanted_lots: &[i64], rms: &R) -> (Vec<String>, Oms, Portfolio)
where
    Q: EventSource<Record = Record>,
    R: Rms,
{
    let trace = Trace::default();
    let mut queue = Recorder {
        inner: queue,
        now: 0,
        trace: trace.clone(),
    };
    let mut strategy = Scripted {
        wanted_lots: wanted_lots.to_vec(),
        candles_seen: 0,
        desired: HashMap::default(),
        trace,
    };
    let (oms, pf) = run(
        &mut queue,
        &mut strategy,
        Oms::default(),
        Portfolio::new(),
        rms,
        &SimClock::new(),
    );
    (strategy.trace.take(), oms, pf)
}

pub fn spy() -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new("SPY", AssetClass::Equity).expect("valid asset"),
        Asset::new("USD", AssetClass::Currency).expect("valid asset"),
        Mic::arcx(),
        Currency::usd(),
    ))
}

/// Signed lots as a position: positive is long, negative short.
pub fn position(lots: i64) -> Position {
    let qty = |n: i64| {
        Quantity::from_str_unchecked(&n.to_string())
            .non_zero()
            .expect("non-zero quantity")
    };
    match lots {
        0 => Position::Flat,
        n if n > 0 => Position::Long(qty(n)),
        n => Position::Short(qty(-n)),
    }
}

/// `"MM:SS.mmm"`: every case runs within an hour.
fn time(ts: i64) -> String {
    DateTime::from_timestamp_nanos(ts)
        .format("%M:%S%.3f")
        .to_string()
}

/// The queue, recording each request the OMS sends at the time of the event that led to it.
struct Recorder<Q> {
    inner: Q,
    now: i64,
    trace: Trace,
}

impl<Q: EventSource> RequestSink for Recorder<Q> {
    fn submit(&mut self, req: Request) {
        let what = match &req {
            Request::SendOrder(order) => format!(
                "send {:?} {:?} {}",
                order.order_type(),
                order.side(),
                order.quantity().qty()
            ),
            other => format!("{other:?}"),
        };
        self.trace
            .borrow_mut()
            .push(format!("{}  {what}", time(self.now)));
        self.inner.submit(req);
    }
}

impl<Q: EventSource<Record = Record>> EventSource for Recorder<Q> {
    type Record = Record;

    fn next_event(&mut self) -> Option<Event<Record>> {
        let event = self.inner.next_event()?;
        self.now = event.ts();
        Some(event)
    }
}

/// Strategy that knows how many lots it wants to own
/// at any moment `T_i` in time.
///
/// Writes records for the tests in `Trace`.
struct Scripted {
    wanted_lots: Vec<i64>,
    candles_seen: usize,
    desired: HashMap<Instrument, Desired>,
    trace: Trace,
}

impl Traded<Record> for Scripted {
    fn on_event(&mut self, event: &Event<Record>, pf: &Portfolio) {
        let what = match event.kind() {
            Kind::MarketData(candle) => {
                let lots = self.wanted_lots[self.candles_seen];
                self.candles_seen += 1;
                let mut want = Desired::new();
                want.set_desired_position(position(lots));
                self.desired.insert(spy(), want);
                format!(
                    "candle {}, held {}, want {lots}",
                    candle.open(),
                    pf.position(&spy())
                )
            }
            Kind::Exec(ExecEvent::Ack(_)) => "ack".to_string(),
            Kind::Exec(ExecEvent::Fill(fill)) => format!(
                "fill {:?} {} @ {}, held {}",
                fill.side(),
                fill.quantity().qty(),
                fill.price(),
                pf.position(&spy())
            ),
            other => format!("{other:?}"),
        };
        self.trace
            .borrow_mut()
            .push(format!("{}  {what}", time(event.ts())));
    }

    fn desired(&self) -> &HashMap<Instrument, Desired> {
        &self.desired
    }
}
