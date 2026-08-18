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

fn qty(q: &str) -> Quantity {
    Quantity::from_str_unchecked(q)
}

fn nz_qty(q: &str) -> NonZeroQuantity {
    qty(q).non_zero().expect("This should be ok")
}

fn px(p: &str) -> Price {
    Price::from_str_unchecked(p)
}

fn build_lmt(instrument: Instrument, qty: NonZeroQuantity, px: Price, side: Side) -> Order<New> {
    OrderBuilder::new(instrument, side, qty)
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
            portfolio.position(&instrument) == &fill.as_position(),
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
    use std::collections::{HashMap, HashSet};

    use lab::{event::Request, oms::Oms, rms::NaiveRms, strategy::Desired};
    use oms::order::FillOutcome;
    use tradeprim::Side;

    use crate::{build_fill, build_lmt, nz_qty, part_eq, px, setup, spy};
    use std::assert_matches;

    /// Desired: 1 order (let it be limit)
    /// Working: 1 order (order above, no fills at all, let's pretend it is unack/just ack)
    /// Real: Zero
    ///
    /// Expected:
    ///     - m = 0
    ///     - d = 1
    #[test]
    fn desired_order_that_is_acked_is_no_op_for_market_sender() {
        let (mut oms, portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);

        // Desire a position
        let q = nz_qty("16");
        let side = Side::Buy;
        let p = px("750.32");
        let order_new = build_lmt(instrument, q, p, side);
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_orders(vec![order_new]);

        // Sending
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        assert_eq!(sink.sent.len(), 1, "{:?}", sink.sent);
        assert_matches!(sink.sent[0], Request::SendOrder(order) if part_eq(&order, &order_new));

        // Unack
        let mut oms = Oms::new(
            HashMap::from_iter([(order_new.order_id(), order_new)]),
            HashMap::new(),
            HashSet::new(),
        );
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        assert_eq!(sink.sent.len(), 1, "{:?}", sink.sent);

        // Ack
        let mut oms = Oms::new(
            HashMap::new(),
            HashMap::from_iter([(order_new.order_id(), order_new.into_working())]),
            HashSet::new(),
        );
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:?}", sink.sent);
    }

    /// Desired: 1 order (let it be limit)
    /// Working: 1 order (order above, partial fill)
    /// Real: Some qty
    ///
    /// Expected: Zero - it's working, it's desired, it changed desired position, no additional actions are required.
    #[test]
    fn partial_fill_of_desired_order_self_corrects_desired_position_thus_no_op() {
        let (mut oms, mut portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);

        // Desire a position
        let q = nz_qty("16");
        let side = Side::Buy;
        let p = px("750.32");
        let order_new = build_lmt(instrument, q, p, side);
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_orders(vec![order_new]);

        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        assert_eq!(sink.sent.len(), 1, "{:?}", sink.sent);
        assert_matches!(sink.sent[0], Request::SendOrder(order) if part_eq(&order, &order_new));

        // Partial fill
        let q = nz_qty("8");
        let px = px("750.32");
        let fill = build_fill(&order_new.into_working(), q, px);
        portfolio.push_fill(fill);
        assert!(
            portfolio.position(&instrument) == &fill.as_position(),
            "{}",
            portfolio.position(&instrument)
        );

        let FillOutcome::Partial(working) = order_new.into_working().apply_fill(&fill) else {
            panic!("16 - 8 = partial")
        };
        // Desired order should mutate strategy.desired_position state to negate its partial fill
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .add_desired_position(fill.as_position());
        let mut oms = Oms::new(
            HashMap::new(),
            HashMap::from_iter([(working.order_id(), working)]),
            HashSet::new(),
        );

        // assert
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
    }
}
