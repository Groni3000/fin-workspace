use std::collections::{HashMap, HashSet};

use crate::{
    event::{Event, EventSource, Request},
    oms::Oms,
    portfolio::Portfolio,
};
use chrono::DateTime;
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use oms::{
    fill::Fill,
    order::{New, Order, OrderBuilder, OrderType, Working},
};
use tradeprim::{
    Side, currency::Currency, position::NonZeroQuantity, price::Price, quantity::Quantity,
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

fn check_oms_state(
    oms: &Oms,
    expected_unacked: usize,
    expected_working: usize,
    expected_pending_cancels: usize,
) {
    assert_eq!(oms.unacked.len(), expected_unacked, "oms:\n{:#?}", oms);
    assert_eq!(oms.working.len(), expected_working, "oms:\n{:#?}", oms);
    assert_eq!(
        oms.pending_cancels.len(),
        expected_pending_cancels,
        "oms:\n{:#?}",
        oms
    );
}

mod reconcile {
    use std::collections::HashMap;

    use crate::{
        event::{Event, Kind, RejectReason, Request},
        oms::tests::{build_lmt, check_oms_state, qty},
        rms::NaiveRms,
        strategy::Desired,
    };
    use oms::order::{OrderType, TerminationReason};
    use tradeprim::{Side, position::Position, quantity::Quantity};

    use super::{build_fill, build_mkt, nz_qty, part_eq, px, setup, spy};
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

    /// Send market, partial fill, no new orders expected, final fill, oms transferred order to portfolio.
    ///
    /// Real oms, portfolio, naive rms, part of strategy (most likely future trait)
    ///
    /// Test sink.
    #[test]
    fn send_market_full_lifetime() {
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

        let order_new = match sink.sent[0] {
            Request::SendOrder(o) => o,
            _ => unreachable!(),
        };
        let id = order_new.order_id();
        // Let's write a "normal" workflow
        // 1. Assert oms state
        check_oms_state(&oms, 1, 0, 0);
        // 2. Imagine some other event arrived, state should not change
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 1, 0, 0);

        // 3. Ack arrived
        let ack_event = Event::new(0, Kind::<()>::Ack(id));
        oms.on_event(&ack_event, &mut portfolio);
        // on_event shoud move order to working, removing from unacked
        check_oms_state(&oms, 0, 1, 0);

        // 4. Partial fill arrived
        let fill_q = nz_qty("10");
        let fill_px = px("100");
        let fill = build_fill(&order_new.into_working(), fill_q, fill_px);
        let fill_event = Event::new(1, Kind::<()>::Fill(fill));
        oms.on_event(&fill_event, &mut portfolio);

        // oms should have pushed fill into the portfolio
        assert!(
            portfolio.position(&instrument) == &fill.as_position(),
            "{}",
            portfolio.position(&instrument)
        );
        // partial fill should not change the state: order is still in working
        check_oms_state(&oms, 0, 1, 0);
        assert_eq!(
            oms.working[&id].state().leaves(),
            qty("6"),
            "oms:\n{:#?}",
            oms
        );

        // should be no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        // No new orders were send
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        // reconcile should not change the state: order is still in working
        check_oms_state(&oms, 0, 1, 0);

        // 5. Full fill arrives
        let fill_q = nz_qty("6");
        let fill_px = px("100");
        let fill = build_fill(&order_new.into_working(), fill_q, fill_px);
        let fill_event = Event::new(2, Kind::<()>::Fill(fill));
        oms.on_event(&fill_event, &mut portfolio);

        // Final asserts: oms should be empty, portfolio should have all fills and a terminated order
        check_oms_state(&oms, 0, 0, 0);
        assert!(
            *portfolio.position(&instrument)
                == match order_new.side() {
                    Side::Buy => Position::Long(order_new.quantity()),
                    Side::Sell => Position::Short(order_new.quantity()),
                },
            "{}",
            portfolio.position(&instrument)
        );
        assert!(portfolio.fills().len() == 2, "{:#?}", portfolio);
        assert!(portfolio.orders().len() == 1, "{:#?}", portfolio);
        assert!(
            portfolio.orders_idx().get(&order_new.order_id()) == Some(&0_usize),
            "{:#?}",
            portfolio
        );
        assert!(
            portfolio.orders()[0].state().leaves() == Quantity::ZERO,
            "{:#?}",
            portfolio
        );
        assert!(
            portfolio.orders()[0].state().reason() == TerminationReason::Filled,
            "{:#?}",
            portfolio
        );
    }

    /// Send market, partial fill, no new orders expected, final fill, oms transferred order to portfolio.
    ///
    /// Real oms, portfolio, naive rms, part of strategy (most likely future trait)
    ///
    /// Test sink.
    #[test]
    fn mkt_and_lmt_full_lifetime() {
        let (mut oms, mut portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);
        let mut mock_ts = 0;

        // Desire a position
        let q = nz_qty("16");
        let side = Side::Buy;
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_position(Position::Long(q));
        let (lmt_q, lmt_s, lmt_p) = (nz_qty("2"), Side::Buy, px("101"));
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_orders(vec![build_lmt(instrument, lmt_q, lmt_p, lmt_s)]);

        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        assert_eq!(sink.sent.len(), 2, "{:?}", sink.sent);
        let expected_lmt = build_lmt(instrument, lmt_q, lmt_p, lmt_s);
        assert_matches!(sink.sent[0], Request::SendOrder(order) if part_eq(&order, &expected_lmt) && order.state() == expected_lmt.state());
        let expected_mkt = build_mkt(instrument, q, side);
        assert_matches!(sink.sent[1], Request::SendOrder(order) if part_eq(&order, &expected_mkt));

        // mkt id
        let mkt_order_new = match sink.sent[1] {
            Request::SendOrder(o) => o,
            _ => unreachable!(),
        };
        let id_mkt = mkt_order_new.order_id();
        // lmt id
        let lmt_order_new = match sink.sent[0] {
            Request::SendOrder(o) => o,
            _ => unreachable!(),
        };
        let id_lmt = lmt_order_new.order_id();
        assert_ne!(id_mkt, id_lmt);
        assert_eq!(mkt_order_new.order_type(), &OrderType::Market);
        assert_eq!(lmt_order_new.order_type(), &OrderType::Limit(lmt_p));

        // Let's write a "normal" workflow
        // 1. Assert oms state
        check_oms_state(&oms, 2, 0, 0);
        // 2. Imagine some other event arrived, state should not change
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 2, 0, 0);

        // 3. Ack arrived
        let ack_event = Event::new(mock_ts, Kind::<()>::Ack(id_mkt));
        mock_ts += 1;
        oms.on_event(&ack_event, &mut portfolio);
        // on_event shoud move order to working, removing from unacked
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 1, 1, 0);

        // 4. Partial MKT fill arrived
        let fill_q = nz_qty("10");
        let fill_px = px("100");
        let fill = build_fill(&mkt_order_new.into_working(), fill_q, fill_px);
        let fill_event = Event::new(mock_ts, Kind::<()>::Fill(fill));
        mock_ts += 1;
        // on_event shoud have change leaves of mkt order and mutate position in Portfolio
        oms.on_event(&fill_event, &mut portfolio);
        // reconcile should be no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 1, 1, 0);

        // oms should have pushed fill into the portfolio
        assert!(
            portfolio.position(&instrument) == &fill.as_position(),
            "{}",
            portfolio.position(&instrument)
        );
        assert_eq!(
            oms.working[&id_mkt].state().leaves(),
            qty("6"),
            "oms:\n{:#?}",
            oms
        );

        // 5. Ack of LMT arrived
        let ack_event = Event::new(mock_ts, Kind::<()>::Ack(id_lmt));
        mock_ts += 1;
        // on_event moves lmt order to working
        oms.on_event(&ack_event, &mut portfolio);
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 2, 0);

        // 6. Partial LMT Fill arrived
        let fill_lmt_q = nz_qty("1");
        let fill_lmt_px = px("101");
        let fill_lmt = build_fill(&lmt_order_new.into_working(), fill_lmt_q, fill_lmt_px);
        let fill_lmt_event = Event::new(mock_ts, Kind::<()>::Fill(fill_lmt));
        mock_ts += 1;
        // on_event mutates `leaves` of lmt order
        oms.on_event(&fill_lmt_event, &mut portfolio);
        // `Strategy` should change desired position for lmt partial fill before `oms.reconcile`
        desired
            .entry(instrument)
            .and_modify(|p| *p.dp_mut() += fill_lmt.as_position());
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 2, 0);

        // oms should have pushed fill into the portfolio
        assert!(portfolio.fills().len() == 2, "{:#?}", portfolio);
        assert!(
            portfolio.position(&instrument)
                == &(fill.as_position() + fill_lmt.as_position()).expect("correct Add"),
            "{:#?}",
            portfolio.position(&instrument)
        );
        let last_known_pf_position = *portfolio.position(&instrument);

        // leaves for MKT order is not changed
        assert_eq!(
            oms.working[&id_mkt].state().leaves(),
            qty("6"),
            "oms:\n{:#?}",
            oms
        );
        // leaves for LMT order is changed
        assert_eq!(
            oms.working[&id_lmt].state().leaves(),
            qty("1"),
            "oms:\n{:#?}",
            oms
        );
        // 7. Full LMT fill arrives
        let fill_lmt_q = nz_qty("1");
        let fill_lmt_px = px("101");
        let fill_lmt = build_fill(&lmt_order_new.into_working(), fill_lmt_q, fill_lmt_px);
        let fill_lmt_event = Event::new(mock_ts, Kind::<()>::Fill(fill_lmt));
        mock_ts += 1;
        // on_event should remove LMT order to portfolio in terminated state
        oms.on_event(&fill_lmt_event, &mut portfolio);
        // `Strategy` should change desired position for lmt partial fill before `oms.reconcile`
        desired
            .entry(instrument)
            .and_modify(|p| *p.dp_mut() += fill_lmt.as_position());
        // `Strategy` should remove desired order from self.desired_orders on full fill.
        desired
            .entry(instrument)
            .and_modify(|e| e.remove_order(id_lmt));
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 1, 0);

        // oms should have pushed fill into the portfolio
        assert!(portfolio.fills().len() == 3, "{:#?}", portfolio);
        assert!(
            portfolio.position(&instrument)
                == &(last_known_pf_position + fill_lmt.as_position()).expect("correct Add"),
            "{:#?}",
            portfolio.position(&instrument)
        );
        let last_known_pf_position = *portfolio.position(&instrument);

        // leaves for MKT order is not changed
        assert_eq!(
            oms.working[&id_mkt].state().leaves(),
            qty("6"),
            "oms:\n{:#?}",
            oms
        );
        assert_eq!(portfolio.orders().len(), 1, "{:?}", portfolio);
        let lmt_terminated = portfolio
            .orders()
            .get(
                *portfolio
                    .orders_idx()
                    .get(&id_lmt)
                    .expect("lmt order should be terminated"),
            )
            .expect("order should be found");
        assert_eq!(
            lmt_terminated.state().leaves(),
            Quantity::ZERO,
            "{:?}",
            portfolio
        );
        assert_eq!(
            lmt_terminated.state().reason(),
            TerminationReason::Filled,
            "{:?}",
            portfolio
        );

        // 8. Full MKT fill arrives
        let fill_q = nz_qty("6");
        let fill_px = px("100");
        let fill = build_fill(&mkt_order_new.into_working(), fill_q, fill_px);
        let fill_event = Event::new(mock_ts, Kind::<()>::Fill(fill));
        // on_event should remove MKT order to portfolio in terminated state
        oms.on_event(&fill_event, &mut portfolio);
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 0, 0);

        // oms should have pushed fill into the portfolio
        assert!(portfolio.fills().len() == 4, "{:#?}", portfolio);
        assert!(
            portfolio.position(&instrument)
                == &(last_known_pf_position + fill.as_position()).expect("correct Add"),
            "{:#?}",
            portfolio.position(&instrument)
        );

        assert_eq!(portfolio.orders().len(), 2, "{:?}", portfolio);
        let mkt_terminated = portfolio
            .orders()
            .get(
                *portfolio
                    .orders_idx()
                    .get(&id_mkt)
                    .expect("mkt order should be terminated"),
            )
            .expect("order should be found");
        assert_eq!(
            mkt_terminated.state().leaves(),
            Quantity::ZERO,
            "{:?}",
            portfolio
        );
        assert_eq!(
            mkt_terminated.state().reason(),
            TerminationReason::Filled,
            "{:?}",
            portfolio
        );
    }

    /// Desired order acked, then dropped by the strategy.
    ///
    /// Expected: one cancel regardless of how many reconciles run, order stays live until the
    /// venue confirms, terminates as `Cancel` with the whole quantity still outstanding.
    #[test]
    fn cancel_acked_desired_order() {
        let (mut oms, mut portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);
        let mut mock_ts = 0;

        let (lmt_q, lmt_s, lmt_p) = (nz_qty("2"), Side::Buy, px("101"));
        let lmt = build_lmt(instrument, lmt_q, lmt_p, lmt_s);
        let id_lmt = lmt.order_id();
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_orders(vec![lmt]);

        // 1. Send
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        assert_matches!(sink.sent[0], Request::SendOrder(order) if part_eq(&order, &lmt));
        check_oms_state(&oms, 1, 0, 0);

        // 2. Ack arrived
        oms.on_event(
            &Event::new(mock_ts, Kind::<()>::Ack(id_lmt)),
            &mut portfolio,
        );
        mock_ts += 1;
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 1, 0);

        // 3. `Strategy` no longer wants the order
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .remove_order(id_lmt);
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        assert_matches!(sink.sent[1], Request::CancelOrder(instr, id) if instr == instrument && id == id_lmt);
        // order is live until the venue confirms
        check_oms_state(&oms, 0, 1, 1);

        // 4. Further reconciles must not re-request the cancel
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 1, 1);

        // 5. Venue confirms the cancel
        oms.on_event(
            &Event::new(mock_ts, Kind::<()>::CancelResponse(id_lmt, true)),
            &mut portfolio,
        );
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 0, 0);

        assert!(portfolio.fills().is_empty(), "{:#?}", portfolio);
        assert_eq!(portfolio.orders().len(), 1, "{:#?}", portfolio);
        let cancelled = &portfolio.orders()[*portfolio
            .orders_idx()
            .get(&id_lmt)
            .expect("cancelled order should be indexed")];
        assert_eq!(
            cancelled.state().reason(),
            TerminationReason::Cancel,
            "{:#?}",
            portfolio
        );
        // nothing filled, so the whole quantity is still outstanding
        assert_eq!(cancelled.state().leaves(), lmt_q.qty(), "{:#?}", portfolio);
    }

    /// Venue rejects a desired order before it is acked.
    ///
    /// Expected: order terminates as `Reject` with full leaves, and the reconcile that follows
    /// does not resend it even though the strategy still desires it.
    #[test]
    fn reject_unacked_desired_order() {
        let (mut oms, mut portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);

        let (lmt_q, lmt_s, lmt_p) = (nz_qty("2"), Side::Buy, px("101"));
        let lmt = build_lmt(instrument, lmt_q, lmt_p, lmt_s);
        let id_lmt = lmt.order_id();
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_orders(vec![lmt]);

        // 1. Send
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 1, 0, 0);

        // 2. Reject arrives before any ack, `Strategy` has not dropped the order yet
        oms.on_event(
            &Event::new(
                0,
                Kind::<()>::Reject(
                    id_lmt,
                    RejectReason::Venue(
                        "Trading during non-RTH is not allowed for this order type".into(),
                    ),
                ),
            ),
            &mut portfolio,
        );
        // a terminated id must never be resent
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 0, 0);

        assert!(portfolio.fills().is_empty(), "{:#?}", portfolio);
        assert_eq!(portfolio.orders().len(), 1, "{:#?}", portfolio);
        let rejected = &portfolio.orders()[*portfolio
            .orders_idx()
            .get(&id_lmt)
            .expect("rejected order should be indexed")];
        assert_eq!(
            rejected.state().reason(),
            TerminationReason::Reject,
            "{:#?}",
            portfolio
        );
        assert_eq!(rejected.state().leaves(), lmt_q.qty(), "{:#?}", portfolio);

        // 3. `Strategy` drops it and nothing else happens
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .remove_order(id_lmt);
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 0, 0);
    }

    /// Venue reports a fill larger than the order.
    ///
    /// Expected: the whole reported quantity moves the position, the order terminates as
    /// `Overfilled`, and a strategy that self-corrects `dp` by the *fill* leaves nothing to do.
    ///
    /// TLDR:
    ///
    ///  Only Strategy decides how to act on overfill of desired order.
    ///  For example: standard actions like it this test - accept it (with a warning in a log).
    ///  Or, it can look that there was an overfill and correct desired position by CORRECT amount
    ///  and Oms will correct position by Market order.
    #[test]
    fn overfill_of_desired_order() {
        let (mut oms, mut portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);
        let mut mock_ts = 0;

        let (lmt_q, lmt_s, lmt_p) = (nz_qty("2"), Side::Buy, px("101"));
        let lmt = build_lmt(instrument, lmt_q, lmt_p, lmt_s);
        let id_lmt = lmt.order_id();
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_orders(vec![lmt]);

        // 1. Send
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 1, 0, 0);

        // 2. Ack arrived
        oms.on_event(
            &Event::new(mock_ts, Kind::<()>::Ack(id_lmt)),
            &mut portfolio,
        );
        mock_ts += 1;
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 1, 0);

        // 3. Build a fill for larger quantity
        let fill = build_fill(&lmt.into_working(), nz_qty("3"), lmt_p);
        // Oms reacts to it
        oms.on_event(&Event::new(mock_ts, Kind::<()>::Fill(fill)), &mut portfolio);
        // Assume that `Strategy` policy is: correct `dp` by what actually filled, not by the order quantity
        let d = desired
            .get_mut(&instrument)
            .expect("should have instrument");
        *d.dp_mut() += fill.as_position();
        d.remove_order(id_lmt);
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        // nothing can fill again, so the order leaves `working`
        check_oms_state(&oms, 0, 0, 0);

        // !!!That overfill is in real position!!!
        assert_eq!(portfolio.fills().len(), 1, "{:#?}", portfolio);
        assert_eq!(
            portfolio.position(&instrument),
            &fill.as_position(),
            "{:#?}",
            portfolio.position(&instrument)
        );
        assert_eq!(portfolio.orders().len(), 1, "{:#?}", portfolio);
        let overfilled = &portfolio.orders()[*portfolio
            .orders_idx()
            .get(&id_lmt)
            .expect("overfilled order should be indexed")];
        assert_eq!(
            overfilled.state().reason(),
            TerminationReason::Overfilled,
            "{:#?}",
            portfolio
        );
        assert_eq!(
            overfilled.state().leaves(),
            Quantity::ZERO,
            "{:#?}",
            portfolio
        );
    }

    /// Venue overfills the market order the OMS sent for `dp`.
    ///
    /// Expected: no strategy action at all - the next reconcile sees
    /// `rp` past it and files the opposite market order for the excess.
    #[test]
    fn overfill_of_desired_position_self_corrects() {
        let (mut oms, mut portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);
        let mut mock_ts = 0;

        // Desire a position
        let q = nz_qty("16");
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_position(Position::Long(q));

        // 1. Send
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        assert_matches!(sink.sent[0], Request::SendOrder(order) if part_eq(&order, &build_mkt(instrument, q, Side::Buy)));
        check_oms_state(&oms, 1, 0, 0);

        let mkt_order_new = match sink.sent[0] {
            Request::SendOrder(o) => o,
            _ => unreachable!(),
        };
        let id_mkt = mkt_order_new.order_id();

        // 2. Ack arrived
        oms.on_event(
            &Event::new(mock_ts, Kind::<()>::Ack(id_mkt)),
            &mut portfolio,
        );
        mock_ts += 1;
        // reconcile is no-op
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 1, 0);

        // 3. Eighteen fill against an order for sixteen
        let fill = build_fill(&mkt_order_new.into_working(), nz_qty("18"), px("100"));
        oms.on_event(&Event::new(mock_ts, Kind::<()>::Fill(fill)), &mut portfolio);
        mock_ts += 1;
        // `Strategy` does nothing: a market order never moved `dp`
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);

        // m = 16 - (0 + 18) = -2
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        let expected_correction = build_mkt(instrument, nz_qty("2"), Side::Sell);
        assert_matches!(sink.sent[1], Request::SendOrder(order) if part_eq(&order, &expected_correction));
        // overfilled order is gone, correction is unacked
        check_oms_state(&oms, 1, 0, 0);

        assert_eq!(portfolio.fills().len(), 1, "{:#?}", portfolio);
        assert_eq!(
            portfolio.position(&instrument),
            &fill.as_position(),
            "{:#?}",
            portfolio.position(&instrument)
        );
        assert_eq!(portfolio.orders().len(), 1, "{:#?}", portfolio);
        let overfilled = &portfolio.orders()[*portfolio
            .orders_idx()
            .get(&id_mkt)
            .expect("order should be in terminated")];
        assert_eq!(
            overfilled.state().reason(),
            TerminationReason::Overfilled,
            "{:#?}",
            portfolio
        );
        assert_eq!(
            overfilled.state().leaves(),
            Quantity::ZERO,
            "{:#?}",
            portfolio
        );

        let correction_new = match sink.sent[1] {
            Request::SendOrder(o) => o,
            _ => unreachable!(),
        };
        let id_correction = correction_new.order_id();

        // 4. Ack of the correction arrived
        oms.on_event(
            &Event::new(mock_ts, Kind::<()>::Ack(id_correction)),
            &mut portfolio,
        );
        mock_ts += 1;
        // in-flight correction must not be sent twice: m = 16 - (-2 + 18) = 0
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 1, 0);

        // 5. Correction fills
        let fill_correction = build_fill(&correction_new.into_working(), nz_qty("2"), px("100"));
        oms.on_event(
            &Event::new(mock_ts, Kind::<()>::Fill(fill_correction)),
            &mut portfolio,
        );
        // reconcile is no-op: rp is back on dp
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 0, 0);

        assert_eq!(portfolio.fills().len(), 2, "{:#?}", portfolio);
        assert_eq!(
            portfolio.position(&instrument),
            &Position::Long(q),
            "{:#?}",
            portfolio.position(&instrument)
        );
        assert_eq!(portfolio.orders().len(), 2, "{:#?}", portfolio);
        let corrected = &portfolio.orders()[*portfolio
            .orders_idx()
            .get(&id_correction)
            .expect("correction order should be indexed")];
        assert_eq!(
            corrected.state().reason(),
            TerminationReason::Filled,
            "{:#?}",
            portfolio
        );
    }

    /// Venue refuses the cancel: "too late". The order reached a terminal state first.
    ///
    /// Mainly occures when we send an order and then immediately cancel it, but venue has already filled
    /// it before the cancel arrives.
    ///
    /// Expected idea: even when we get `CancelResponse(id, false)`, we keep it in pending cancels assuming
    /// that the only way it can happen - an order is filled.
    ///
    /// Why we assume this? Well... The only way to build an order - is to use OrderBuilder. Order does not
    /// expose OrderId and that id is immutable. We cut off the possibility of a custom OrderId being used.
    /// Therfore we don't expect any type of Venue response such as `OrderIsNotFound` or something like this.
    ///
    /// Yet... It's possible to send order, send cancel and get order is not found when sending order failed/took longer to deliver...
    /// TODO: I need to think about this...
    #[test]
    fn cancel_refused_because_the_order_was_already_filling() {
        let (mut oms, mut portfolio, mut sink) = setup();
        let instrument = spy();
        let rms = NaiveRms;
        let mut desired = HashMap::from_iter([(instrument, Desired::new())]);
        let mut mock_ts = 0;

        let q = nz_qty("2");
        let lmt = build_lmt(instrument, q, px("101"), Side::Buy);
        let id_lmt = lmt.order_id();
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .set_desired_orders(vec![lmt]);

        // 1. Send
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 1, 0, 0);

        // 2. Ack arrived
        oms.on_event(
            &Event::new(mock_ts, Kind::<()>::Ack(id_lmt)),
            &mut portfolio,
        );
        mock_ts += 1;
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 1, "{:#?}", sink.sent);
        check_oms_state(&oms, 0, 1, 0);

        // 3. `Strategy` drops the order
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .remove_order(id_lmt);
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        assert_matches!(sink.sent[1], Request::CancelOrder(instr, id) if instrument == instr && id == id_lmt);
        check_oms_state(&oms, 0, 1, 1);

        // 4. Too late: the order had already filled when the venue read the request
        oms.on_event(
            &Event::new(mock_ts, Kind::<()>::CancelResponse(id_lmt, false)),
            &mut portfolio,
        );
        mock_ts += 1;
        // a `false` is terminal, never retried, however many events go by
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        // the order is still on our books: only the fill can resolve it
        check_oms_state(&oms, 0, 1, 1);

        // 5. The fill the venue was talking about arrives
        let fill = build_fill(&lmt.into_working(), q, px("101"));
        oms.on_event(&Event::new(mock_ts, Kind::<()>::Fill(fill)), &mut portfolio);
        desired
            .get_mut(&instrument)
            .expect("should have instrument")
            .add_desired_position(fill.as_position());
        oms.reconcile(&desired, &portfolio, &rms, &mut sink);
        assert_eq!(sink.sent.len(), 2, "{:#?}", sink.sent);
        // the terminating fill drains `pending_cancels` too
        check_oms_state(&oms, 0, 0, 0);

        assert_eq!(portfolio.fills().len(), 1, "{:#?}", portfolio);
        assert_eq!(portfolio.orders().len(), 1, "{:#?}", portfolio);
        let filled = &portfolio.orders()[*portfolio
            .orders_idx()
            .get(&id_lmt)
            .expect("filled order should be indexed")];
        // the cancel lost the race: the order is Filled, not Cancel
        assert_eq!(
            filled.state().reason(),
            TerminationReason::Filled,
            "{:#?}",
            portfolio
        );
        assert_eq!(filled.state().leaves(), Quantity::ZERO, "{:#?}", portfolio);
    }
}
