use std::collections::{HashMap, HashSet};

use chrono::DateTime;
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use lab::{
    event::{Event, EventSource, Request},
    oms::Oms,
    portfolio::Portfolio,
};
use oms::{
    fill::Fill,
    order::{New, Order, OrderBuilder, OrderType, Working},
};
use tradeprim::{
    Side,
    currency::Currency,
    position::{NonZeroQuantity, Position},
    price::Price,
    quantity::Quantity,
};

#[derive(Default)]
struct TestSink {
    sent: Vec<Request>,
}

impl TestSink {
    fn new() -> Self {
        Self { sent: Vec::new() }
    }
}

impl EventSource for TestSink {
    type Record = ();
    fn next_event(&mut self) -> Option<Event<()>> {
        None
    }
    fn submit(&mut self, req: Request) {
        self.sent.push(req);
    }
}

#[derive(Debug, Default)]
pub struct Desired {
    desired_position: Position,
    desired_orders: Vec<Order<New>>,
}

impl Desired {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn dp(&self) -> &Position {
        &self.desired_position
    }

    pub fn des_ords(&self) -> &Vec<Order<New>> {
        &self.desired_orders
    }
}

fn spy() -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new("SPY", AssetClass::Equity).expect("SPY is a valid asset name"),
        Asset::new("USD", AssetClass::Currency).expect("USD is a valid asset name"),
        Mic::arcx(),
        Currency::usd(),
    ))
}

fn reconcile(
    instrument: Instrument,
    desired: &Desired,
    working: &HashMap<Instrument, Vec<Order<Working>>>,
    real_positions: &HashMap<Instrument, Position>,
) -> i64 {
    let ev = vec![];

    let dp_raw = desired.dp();
    let wo_l_q_raw = working.get(&instrument).unwrap_or(&ev);
    let rp_raw = real_positions.get(&instrument).unwrap_or(&Position::Flat);

    let dp = dp_raw.as_i64();
    let mkt_wo_l_q = wo_l_q_raw
        .iter()
        .filter(|o| o.order_type() == &OrderType::Market)
        .map(|o| o.side().as_i64() * o.state().leaves().value() as i64)
        .sum::<i64>();
    let rp = rp_raw.as_i64();

    let _ = dbg!(
        dp,
        mkt_wo_l_q,
        rp,
        dp - (mkt_wo_l_q + rp),
        "dp - (mkt_wo_l_q + rp)"
    );

    dp - (mkt_wo_l_q + rp)
}

fn qty(q: &str) -> Quantity {
    Quantity::from_str_unchecked(q)
}

fn nz_qty(q: &str) -> NonZeroQuantity {
    qty(q).non_zero().expect("This should be ok")
}

fn px(p: &str) -> Price {
    Price::from_str_unchecked(p)
}

fn build_lmt(instrument: Instrument, qty: NonZeroQuantity, px: Price) -> Order<New> {
    OrderBuilder::new(instrument, Side::Buy, qty)
        .with_order_type(OrderType::Limit(px))
        .verify()
        .expect("Limit order with all other default values must be ok to build")
        .build()
}

fn build_mkt(instrument: Instrument, qty: NonZeroQuantity, side: Side) -> Order<New> {
    OrderBuilder::new(instrument, side, qty)
        .verify()
        .expect("Limit order with all other default values must be ok to build")
        .build()
}

fn setup() -> (Oms, Portfolio, TestSink) {
    (
        Oms::new(HashMap::default(), HashMap::default(), HashSet::default()),
        Portfolio::new(),
        TestSink::new(),
    )
}

fn part_eq<T>(order_1: &Order<T>, order_2: &Order<T>) -> bool {
    order_1.instrument() == order_2.instrument()
        && order_1.order_type() == order_2.order_type()
        && order_1.side() == order_2.side()
        && order_1.quantity() == order_2.quantity()
        && order_1.time_in_force() == order_2.time_in_force()
}

fn build_fill(order: &Order<Working>, q: NonZeroQuantity, px: Price) -> Fill {
    Fill::new(
        order.order_id(),
        DateTime::from_timestamp_nanos(0),
        order.instrument(),
        order.side(),
        q,
        px,
    )
}

mod dp {
    use std::collections::{HashMap, HashSet};

    use lab::{event::Request, oms::Oms, rms::NaiveRms, strategy::Desired};
    use oms::order::FillOutcome;
    use tradeprim::{Side, position::Position};

    use crate::{build_fill, build_mkt, nz_qty, part_eq, px, setup, spy};
    use std::assert_matches;

    /// Desired = zero, working = zero, real = zero
    ///
    /// Expected: no market order qty to be sent.
    #[test]
    fn simple_flat() {
        let (mut oms, portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let desired = HashMap::from_iter([(instrument, Desired::new())]);

        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        assert!(sink.sent.is_empty());
    }

    /// Desired: N Pos
    /// Working: Zero
    /// Real: Zero
    ///
    /// Expected: make a market order with desired qty
    #[test]
    fn send_market() {
        let (mut oms, portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);

        // Desire a position
        let q = nz_qty("16");
        let side = Side::Buy;
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_position(Position::Long(q));

        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        assert_eq!(sink.sent.len(), 1);
        let expected = build_mkt(instrument, q, side);
        assert_matches!(sink.sent[0], Request::SendOrder(order) if part_eq(&order, &expected));
    }

    /// Send market, partial fill, no new orders expected
    #[test]
    fn send_market_part_fill_no_op() {
        let (mut oms, mut portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);

        // Desire a position
        let q = nz_qty("16");
        let side = Side::Buy;
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_position(Position::Long(q));

        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        assert_eq!(sink.sent.len(), 1, "{:?}", sink.sent);
        let expected = build_mkt(instrument, q, side);
        assert_matches!(sink.sent[0], Request::SendOrder(order) if part_eq(&order, &expected));

        // Partial fill
        let order_new = match sink.sent[0] {
            Request::SendOrder(o) => o,
            _ => unreachable!(),
        };
        let fill_q = nz_qty("10");
        let fill_px = px("100");
        let fill = build_fill(&order_new.into_working(), fill_q, fill_px);
        portfolio.push_fill(fill);
        assert!(
            portfolio.position(&instrument) == &Position::Long(fill_q),
            "{}",
            portfolio.position(&instrument)
        );
        let FillOutcome::Partial(working) = order_new.into_working().apply_fill(&fill) else {
            panic!("16 minus 10 should be partial")
        };
        let oms_working = HashMap::from([(order_new.order_id(), working)]);
        let mut oms = Oms::new(HashMap::default(), oms_working, HashSet::default());

        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        // No new orders were send
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
    }
}

mod d_o {
    use std::collections::HashMap;

    use instrid::instruments::Instrument;
    use oms::order::{Order, Working};
    use tradeprim::{position::Position, quantity::Quantity};

    use crate::{Desired, build_lmt, nz_qty, px, reconcile, spy};

    /// Desired: 1 order (let it be limit)
    /// Working: 1 order (order above, no fills at all, let's pretend it is unack/just ack)
    /// Real: Zero
    ///
    /// Expected: Zero - it's working, it's desired, no additional actions are required.
    #[test]
    fn desired_order_that_is_acked_is_no_op() {
        let instrument = spy();
        let mut desired = Desired::new();

        // We have 1 order (it doesn't matter unack or ack, just working)
        let order_new = build_lmt(instrument, nz_qty("16"), px("750.32"));
        let order_working = order_new.into_working();

        // Flat means we want to be flat
        desired.desired_position = Position::Flat;
        desired.desired_orders = vec![order_new];
        let working: HashMap<Instrument, Vec<Order<Working>>> =
            HashMap::from([(instrument, vec![order_working])]);
        // No real positions
        let real_positions: HashMap<Instrument, Position> = HashMap::default();
        // Expect no market orders to be reconciled
        let m_ords_raw_qty = reconcile(instrument, &desired, &working, &real_positions);
        assert_eq!(m_ords_raw_qty.unsigned_abs(), Quantity::ZERO.value());
    }

    /// Desired: 1 order (let it be limit)
    /// Working: 1 order (order above, partial fill)
    /// Real: Some qty
    ///
    /// Expected: Zero - it's working, it's desired, it changed desired position, no additional actions are required.
    #[test]
    fn partial_fill_of_desired_order_self_corrects_desired_position_thus_no_op() {
        let instrument = spy();
        let mut desired = Desired::new();

        // We have 1 order (it doesn't matter unack or ack, just working)
        let order_new = build_lmt(instrument, nz_qty("16"), px("750.32"));
        let order_working = order_new.into_working();
        // Flat means we want to be flat
        desired.desired_position = Position::Flat;
        desired.desired_orders = vec![order_new];
        let working: HashMap<Instrument, Vec<Order<Working>>> =
            HashMap::from([(instrument, vec![order_working])]);
        // No real positions
        let real_positions: HashMap<Instrument, Position> = HashMap::default();
        // Expect no market orders to be reconciled
        let m_ords_raw_qty = reconcile(instrument, &desired, &working, &real_positions);
        assert_eq!(m_ords_raw_qty.unsigned_abs(), Quantity::ZERO.value());
    }
}
