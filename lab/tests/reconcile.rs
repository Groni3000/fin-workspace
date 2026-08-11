use std::collections::HashMap;

use chrono::DateTime;
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use oms::{
    fill::Fill,
    order::{FillOutcome, New, Order, OrderBuilder, OrderType, Working},
};
use tradeprim::{Side, currency::Currency, position::Position, price::Price, quantity::Quantity};

#[derive(Debug, Default)]
pub struct Desired {
    desired_position: Position,
    desired_orders: Vec<Order<New>>,
    desired_protected_position: Position,
    desired_protective_orders: Vec<Order<New>>,
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

    pub fn dpp(&self) -> &Position {
        &self.desired_protected_position
    }

    pub fn des_prot_ords(&self) -> &Vec<Order<New>> {
        &self.desired_protective_orders
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

// M = dp + sum(des_ords) + (dpp + sum(des_prot_ords)) - sum(wo_l_q) - rp
fn reconcile(
    instrument: Instrument,
    desired: &Desired,
    working: &HashMap<Instrument, Vec<Order<Working>>>,
    real_positions: &HashMap<Instrument, Position>,
) -> i64 {
    let ev = vec![];

    let dp = desired.dp();
    let des_ords = desired.des_ords();
    let dpp = desired.dpp();
    let des_prot_ords = desired.des_prot_ords();
    let wo_l_q = working.get(&instrument).unwrap_or(&ev);
    let rp = real_positions.get(&instrument).unwrap_or(&Position::Flat);

    let dp_raw = dp.as_i64();
    let des_ords_raw = des_ords
        .iter()
        .map(|o| o.side().as_i64() * o.quantity().value() as i64)
        .sum::<i64>();
    let des_prot_ords_raw = des_prot_ords
        .iter()
        .map(|o| o.side().as_i64() * o.quantity().value() as i64)
        .sum::<i64>();
    let wo_l_q_raw = wo_l_q
        .iter()
        .map(|o| o.side().as_i64() * o.state().leaves().value() as i64)
        .sum::<i64>();
    let rp_raw = rp.as_i64();

    let _ = dbg!(
        dp_raw,
        des_ords_raw,
        dpp.as_i64(),
        des_prot_ords_raw,
        wo_l_q_raw,
        rp_raw,
        "M = dp + sum(des_ords) + (dpp + sum(des_prot_ords)) - sum(wo_l_q) - rp"
    );

    dp_raw + des_ords_raw + (dpp.as_i64() + des_prot_ords_raw) - wo_l_q_raw - rp_raw
}

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
    let qty = Quantity::from_str_unchecked("16")
        .non_zero()
        .expect("This should be ok");
    let order_new = OrderBuilder::new(instrument, Side::Buy, qty)
        .with_order_type(OrderType::Limit(Price::from_str_unchecked("750.32")))
        .verify()
        .expect("Limit order with all other default values must be ok to build")
        .build();
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
/// Working: 1 order (order above, partially filled)
/// Real: That partial fill amount
///
/// Expected: Zero - it's working, it's desired, no additional actions are required.
#[test]
fn desired_order_that_is_part_filled_is_no_op() {
    let instrument = spy();
    let mut desired = Desired::new();

    // We have 1 order (it doesn't matter unack or ack, just working)
    let qty = Quantity::from_str_unchecked("16")
        .non_zero()
        .expect("This should be ok");
    let ord_type = OrderType::Limit(Price::from_str_unchecked("750.32"));
    let order_new = OrderBuilder::new(instrument, Side::Buy, qty)
        .with_order_type(ord_type)
        .verify()
        .expect("Limit order with all other default values must be ok to build")
        .build();
    let mut order_working = order_new.into_working();
    let fill = Fill::new(
        order_working.order_id(),
        DateTime::from_timestamp_nanos(1_662_921_288_000_000_000),
        instrument,
        order_working.side(),
        Quantity::ONE.non_zero().expect("One is safe"),
        match ord_type {
            OrderType::Limit(price) => price,
            _ => panic!("This is limit order"),
        },
    );
    order_working = match order_working.apply_fill(&fill) {
        FillOutcome::Partial(order) => order,
        FillOutcome::Filled(_) => panic!("Filled should not happen"),
        FillOutcome::Overfill(_, _) => panic!("Overfill should not happen"),
    };
    // Flat means we want to be flat
    desired.desired_position = Position::Flat;
    desired.desired_orders = vec![order_new];
    let working: HashMap<Instrument, Vec<Order<Working>>> =
        HashMap::from([(instrument, vec![order_working])]);
    // No real positions
    let real_positions: HashMap<Instrument, Position> =
        HashMap::from([(instrument, fill.as_position())]);
    // Expect no market orders to be reconciled
    let m_ords_raw_qty = reconcile(instrument, &desired, &working, &real_positions);
    assert_eq!(m_ords_raw_qty.unsigned_abs(), Quantity::ZERO.value());
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

    // We have 1 order (it doesn't matter unack or ack, just working)
    let qty = Quantity::from_str_unchecked("16")
        .non_zero()
        .expect("This should be ok");
    desired.desired_position = Position::Long(qty);
    let working: HashMap<Instrument, Vec<Order<Working>>> = HashMap::default();
    // No real positions
    let real_positions: HashMap<Instrument, Position> = HashMap::default();
    let m_ords_raw_qty = reconcile(instrument, &desired, &working, &real_positions);
    assert!(m_ords_raw_qty.is_positive());
    assert_eq!(m_ords_raw_qty.unsigned_abs(), qty.value());
}

/// Desired: 1 protected market order, but ZERO protective orders
/// Working: zero
/// Real: zero
///
/// Expected: send market order. This should behave as a simple `dp` (desired_position).
///
/// BUT. This means you did construct it by hand. Which is not a good choice.
#[test]
fn protected_market_with_no_protective_order_behaves_like_simple_desired_position() {
    let instrument = spy();
    let mut desired = Desired::new();

    // We have 1 order (it doesn't matter unack or ack, just working)
    let qty = Quantity::from_str_unchecked("16")
        .non_zero()
        .expect("This should be ok");
    // Flat means we want to be flat
    desired.desired_protected_position = Position::Long(qty);
    let working: HashMap<Instrument, Vec<Order<Working>>> = HashMap::default();
    // No real positions
    let real_positions: HashMap<Instrument, Position> = HashMap::default();
    // Expect no market orders to be reconciled
    let m_ords_raw_qty = reconcile(instrument, &desired, &working, &real_positions);
    assert!(m_ords_raw_qty.is_positive());
    assert_eq!(m_ords_raw_qty.unsigned_abs(), qty.value());
}

/// Desired: 1 protective order (in working) with desired negated market order
/// (not in working, we simulate last step when we send netted desired market order)
/// Working: desired protective order only
/// Real: Zero
///
/// Expected: send market order for a negated qty
#[test]
fn protective_order_sends_market_order_it_protects_and_changes_dpp() {
    let instrument = spy();
    let mut desired = Desired::new();

    // We have 1 order (it doesn't matter unack or ack, just working)
    let qty = Quantity::from_str_unchecked("16")
        .non_zero()
        .expect("This should be ok");
    let ord_type = OrderType::Limit(Price::from_str_unchecked("750.32"));
    let order_new = OrderBuilder::new(instrument, Side::Buy, qty)
        .with_order_type(ord_type)
        .verify()
        .expect("Limit order with all other default values must be ok to build")
        .build();
    let protective_order = order_new.into_working();
    desired.desired_protective_orders = vec![order_new];
    desired.desired_protected_position = match (qty, order_new.side()) {
        (_, Side::Buy) => Position::Short(qty),
        (_, Side::Sell) => Position::Long(qty),
    };

    let working: HashMap<Instrument, Vec<Order<Working>>> =
        HashMap::from([(instrument, vec![protective_order])]);
    // No real positions
    let real_positions: HashMap<Instrument, Position> = HashMap::default();
    // Expect -qty market orders to be reconciled
    let m_ords_raw_qty = reconcile(instrument, &desired, &working, &real_positions);
    assert!(m_ords_raw_qty.is_negative());
    assert_eq!(m_ords_raw_qty.unsigned_abs(), qty.value());
}
