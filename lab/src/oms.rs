use std::collections::HashMap;

use instrid::instruments::Instrument;
use oms::{
    OrderId,
    fill::Fill,
    order::{FillOutcome, New, Order, OrderBuilder, Working},
};
use tradeprim::{Side, quantity::Quantity};

use crate::{
    event::{Event, EventSource, Kind, Request},
    portfolio::Portfolio,
    strategy::Desired,
};

pub struct Oms {
    unacked: HashMap<OrderId, Order<New>>,
    working: HashMap<OrderId, Order<Working>>,
}

impl Oms {
    pub fn new(
        unacked: HashMap<OrderId, Order<New>>,
        working: HashMap<OrderId, Order<Working>>,
    ) -> Self {
        Self { unacked, working }
    }

    pub fn on_event<R>(&mut self, event: &Event<R>, pf: &mut Portfolio) {
        match event.kind() {
            Kind::Ack(id) => {
                self.on_ack(id);
            }
            Kind::Fill(f) => {
                self.on_fill(f, pf);
            }
            Kind::Reject(id) => {
                self.unacked.remove(id);
            }
            _ => {}
        }
    }

    /// remove from unacked and insert into working, converting state to `Working`
    fn on_ack(&mut self, order_id: &OrderId) {
        if let Some(order) = self.unacked.remove(order_id) {
            self.working.insert(*order_id, order.into_working());
        }
    }

    fn on_fill(&mut self, fill: &Fill, pf: &mut Portfolio) {
        // regardless - push fill - it's reported by executor => it's real
        pf.push_fill(*fill);

        match self.working.remove(&fill.order_id()) {
            Some(working_order) => match working_order.apply_fill(fill) {
                FillOutcome::Filled(terminated) => {
                    // push to portfolio
                    pf.push_order(terminated);
                }
                FillOutcome::Partial(working) => {
                    // return order to working
                    self.working.insert(fill.order_id(), working);
                }
                FillOutcome::Overfill(working, _qty) => {
                    // return order to working, notify about overfill
                    self.working.insert(fill.order_id(), working);
                    // TODO: notify about overfill
                }
            },
            None => {} // TODO: notify about fill for an order we don't know (but real position still moved)
        }
    }

    fn desired_orders_qty(&self, orders: &HashMap<OrderId, Order<New>>) -> i64 {
        orders
            .values()
            .map(|o| o.side().as_i64() * o.quantity().value() as i64)
            .sum()
    }

    fn leaves_qty(&self, instrument: &Instrument) -> i64 {
        self.unacked
            .values()
            .filter(|o| &o.instrument() == instrument)
            .map(|o| o.side().as_i64() * o.quantity().value() as i64)
            .sum::<i64>()
            + self
                .working
                .values()
                .filter(|o| &o.instrument() == instrument)
                .map(|o| o.side().as_i64() * o.state().leaves().value() as i64)
                .sum::<i64>()
    }

    /// Sends desired not-market orders to the OMS and Executor.
    fn send_desired_orders<S: EventSource>(
        &mut self,
        desired: &HashMap<Instrument, Desired>,
        sink: &mut S,
    ) {
        for instrument_desired in desired.values() {
            for (id, order) in instrument_desired.orders() {
                let order = *order;
                if self.unacked.contains_key(id) || self.working.contains_key(id) {
                    continue;
                }

                self.unacked.insert(*id, order); // Add to OMS state
                sink.submit(Request::SendOrder(order)); // OMS -> Executor
            }
        }
    }

    /// Sends market orders.
    ///
    /// Must be called the last:
    ///     **all manipulations with desired state and OMS state must be done before this.**
    fn send_market_orders<S: EventSource>(
        &mut self,
        desired: &HashMap<Instrument, Desired>,
        pf: &Portfolio,
        sink: &mut S,
    ) {
        for (instr, want) in desired {
            let m = &want.position().as_i64()      // DP
                  + self.desired_orders_qty(want.orders())  // + sum(DO_q)
                  - self.leaves_qty(instr)//                // - sum(WO_lq)
                  - &pf.position(instr).as_i64(); //    // - RP
            // skip case
            if m == 0 {
                continue;
            }

            let side = if m > 0 { Side::Buy } else { Side::Sell };
            let order = OrderBuilder::new(
                *instr,
                side,
                Quantity::new(m.unsigned_abs())
                    .expect("quantity overflow")
                    .non_zero()
                    .unwrap(),
            )
            .verify()
            .unwrap()
            .build();
            self.unacked.insert(order.order_id(), order);
            sink.submit(Request::SendOrder(order)); // OMS -> Executor
        }
    }

    /// Compare desired state to actual state and send orders to close the gap.
    pub fn reconcile<S: EventSource>(
        &mut self,
        desired: &HashMap<Instrument, Desired>,
        pf: &Portfolio,
        sink: &mut S,
    ) {
        self.send_desired_orders(desired, sink);

        // MUST BE CALLED LAST
        self.send_market_orders(desired, pf, sink);
    }
}
