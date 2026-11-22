use std::{
    fmt::Debug,
    sync::{Arc, Mutex},
};

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
use tracing::{
    Level, Subscriber,
    field::{Field, Visit},
};
use tracing_subscriber::{
    Layer,
    layer::{Context, SubscriberExt},
};
use tradeprim::{currency::Currency, position::Position, quantity::Quantity};

pub type Record = Tagged<Ohlcv>;

/// The log target of the lines the queue wrapper and the strategy write for the trace.
const TRACE: &str = "trace";

/// Initially, we wanted `Trace = Vec<String>`, but had to use Rc<RefCell<T>>,
/// then I saw that some tests would produce noise, and in order to
/// show that, I had to use tracing log lines, but it requires `Send+Sync`,
/// so, here we are, `Arc<Mutex<T>>`.
type Trace = Arc<Mutex<Vec<String>>>;

/// Runs the scripted strategy over `queue` (with some executor).
///
/// The trace is what the run logged: the strategy's events and the requests that reached the
/// queue (target `trace`), plus every warning and error from anywhere.
///
/// Returns its trace, the OMS and the final portfolio.
pub fn run_scripted<Q, R>(queue: Q, wanted_lots: &[i64], rms: &R) -> (Vec<String>, Oms, Portfolio)
where
    Q: EventSource<Record = Record>,
    R: Rms,
{
    let trace = Trace::default();
    let clock = SimClock::new();
    let capture = Capture {
        trace: trace.clone(),
        clock: clock.clone(),
    };
    let mut queue = Recorder { inner: queue };
    let mut strategy = Scripted {
        wanted_lots: wanted_lots.to_vec(),
        candles_seen: 0,
        desired: HashMap::default(),
    };
    // Only for this call and this thread: tests running in parallel don't see each other's logs.
    let subscriber = tracing_subscriber::registry().with(capture);
    let (oms, pf) = tracing::subscriber::with_default(subscriber, || {
        run(
            &mut queue,
            &mut strategy,
            Oms::default(),
            Portfolio::new(),
            rms,
            &clock,
        )
    });
    let lines = std::mem::take(&mut *trace.lock().expect("not poisoned"));

    (lines, oms, pf)
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

/// The queue, logging each request that reaches it. That's what was really sent, independent
/// of what the OMS logs about it.
struct Recorder<Q> {
    inner: Q,
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
        tracing::info!(target: TRACE, "{what}");
        self.inner.submit(req);
    }
}

impl<Q: EventSource<Record = Record>> EventSource for Recorder<Q> {
    type Record = Record;

    fn next_event(&mut self) -> Option<Event<Record>> {
        self.inner.next_event()
    }
}

/// Strategy that knows how many lots it wants to own
/// at any moment `T_i` in time.
///
/// Logs every event it sees, for the trace.
struct Scripted {
    wanted_lots: Vec<i64>,
    candles_seen: usize,
    desired: HashMap<Instrument, Desired>,
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
        tracing::info!(target: TRACE, "{what}");
    }

    fn desired(&self) -> &HashMap<Instrument, Desired> {
        &self.desired
    }
}

/// Fills the trace from the log, at the simulated time: every line with target `trace`, and
/// every warning and error from anywhere, prefixed with its level.
struct Capture {
    trace: Trace,
    clock: SimClock,
}

impl<S: Subscriber> Layer<S> for Capture {
    fn on_event(&self, event: &tracing::Event<'_>, _ctx: Context<'_, S>) {
        let meta = event.metadata();
        let level = *meta.level();
        let mut message = Message::default();
        event.record(&mut message);
        let line = if meta.target() == TRACE {
            message.0
        // In `tracing`, less verbose is smaller: ERROR < WARN < INFO.
        } else if level <= Level::WARN {
            format!("{level} {}", message.0)
        } else {
            return;
        };
        let now = time(self.clock.get());
        self.trace
            .lock()
            .expect("not poisoned")
            .push(format!("{now}  {line}"));
    }
}

/// The `message` field of a log line, without the other fields.
#[derive(Default)]
struct Message(String);

impl Visit for Message {
    fn record_debug(&mut self, field: &Field, value: &dyn Debug) {
        if field.name() == "message" {
            self.0 = format!("{value:?}");
        }
    }
}
