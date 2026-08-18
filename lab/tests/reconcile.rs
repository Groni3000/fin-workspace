use std::collections::HashMap;

use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use oms::order::{New, Order, OrderBuilder, OrderType, Working};
use tradeprim::{
    Side,
    currency::Currency,
    position::{NonZeroQuantity, Position},
    price::Price,
    quantity::Quantity,
};

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

fn build_mkt(instrument: Instrument, qty: NonZeroQuantity) -> Order<New> {
    OrderBuilder::new(instrument, Side::Buy, qty)
        .verify()
        .expect("Limit order with all other default values must be ok to build")
        .build()
}

mod dp {
    use std::collections::HashMap;

    use instrid::instruments::Instrument;
    use oms::order::{Order, Working};
    use tradeprim::position::Position;

    use crate::{Desired, nz_qty, reconcile, spy};

    /// Desired = zero, working = zero, real = zero
    ///
    /// Expected: no market order qty to be sent.
    #[test]
    fn simple_flat() {
        let instrument = spy();
        let mut desired = Desired::new();

        // Flat means we want to be flat
        desired.desired_position = Position::Flat;
        // No working orders
        let working: HashMap<Instrument, Vec<Order<Working>>> = HashMap::default();
        // No real positions
        let real_positions: HashMap<Instrument, Position> = HashMap::default();
        // Expect no market orders to be reconciled
        let m_ords_qty = reconcile(instrument, &desired, &working, &real_positions);
        assert_eq!(m_ords_qty, 0);
    }

    /// Desired: 1 Pos
    /// Working: Zero
    /// Real: Zero
    ///
    /// Expected: make a market order with desired qty
    #[test]
    fn send_market() {
        let instrument = spy();
        let mut desired = Desired::new();

        // Set desired position
        let q = nz_qty("16");
        desired.desired_position = Position::Long(q);

        // Nothing in working
        let working: HashMap<Instrument, Vec<Order<Working>>> = HashMap::default();
        // No real positions
        let real_positions: HashMap<Instrument, Position> = HashMap::default();

        // Expect to send a market order with respect to its sign
        let m_ords_raw_qty = reconcile(instrument, &desired, &working, &real_positions);
        assert!(m_ords_raw_qty.is_positive());
        assert_eq!(m_ords_raw_qty.unsigned_abs(), q.value());
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
