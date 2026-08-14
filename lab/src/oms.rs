use std::collections::{HashMap, HashSet};

use instrid::instruments::Instrument;
use oms::{
    OrderId,
    fill::Fill,
    order::{FillOutcome, New, Order, OrderBuilder, OrderType, Working},
};
use tradeprim::{Side, quantity::Quantity};

use crate::{
    event::{Event, EventSource, Kind, Request},
    portfolio::Portfolio,
    rms::Rms,
    strategy::Desired,
};

#[derive(Default)]
pub struct Oms {
    unacked: HashMap<OrderId, Order<New>>,
    working: HashMap<OrderId, Order<Working>>,
    pending_cancels: HashSet<OrderId>,
}

impl Oms {
    pub fn new(
        unacked: HashMap<OrderId, Order<New>>,
        working: HashMap<OrderId, Order<Working>>,
        pending_cancels: HashSet<OrderId>,
    ) -> Self {
        Self {
            unacked,
            working,
            pending_cancels,
        }
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
                self.on_reject(id, pf);
            }
            Kind::CancelResponse(id, success) => {
                self.on_cancel_response(id, success, pf);
            }
            Kind::MarketData(_) => {
                // This oms is not concerned with market data
            }
            Kind::FeedError(_) => {
                // This oms is not concerned with feed errors
            }
        }
    }

    fn on_reject(&mut self, order_id: &OrderId, pf: &mut Portfolio) {
        tracing::warn!(order_id = ?order_id, "reject");
        // Rejected order may be in both unacked or working.
        //
        // Just push it to the portfolio as is.
        let order = self
            .unacked
            .remove(order_id)
            .map(Order::into_working)
            .or_else(|| self.working.remove(order_id));

        match order {
            Some(o) => pf.push_order(o.into_rejected()),
            None => tracing::warn!(order_id = ?order_id, "reject for unknown order"),
        }
    }

    /// remove from unacked and insert into working, converting state to `Working`
    fn on_ack(&mut self, order_id: &OrderId) {
        if let Some(order) = self.unacked.remove(order_id) {
            tracing::debug!(order_id = ?order_id, side = ?order.side(), qty = %order.quantity().qty(), "ack");
            self.working.insert(*order_id, order.into_working());
        } else {
            // There may be case where Ack arrives after Fill (which means order can be in working).
            if !self.working.contains_key(order_id) {
                tracing::warn!(order_id = ?order_id, "ack for unknown order");
            }
        }
    }

    fn on_fill(&mut self, fill: &Fill, pf: &mut Portfolio) {
        // regardless - push fill - it's reported by executor => it's real
        pf.push_fill(*fill);
        tracing::info!(
            order_id = ?fill.order_id(),
            instrument = %fill.instrument(),
            side = ?fill.side(),
            qty = %fill.quantity().qty(),
            price = %fill.price(),
            position = %pf.position(&fill.instrument()),
            "fill"
        );
        let order = self.working.remove(&fill.order_id()).or_else(|| {
            self.unacked
                .remove(&fill.order_id())
                .map(|o| o.into_working())
        });

        match order {
            Some(working_order) => match working_order.apply_fill(fill) {
                FillOutcome::Filled(terminated) => {
                    // push to portfolio
                    pf.push_order(terminated);
                }
                FillOutcome::Partial(working) => {
                    // return order to working
                    self.working.insert(fill.order_id(), working);
                }
                FillOutcome::Overfill(terminated, excess) => {
                    // Order is terminated: it can never fill again. The excess is already in `pf`.
                    tracing::error!(order_id = ?fill.order_id(), excess = %excess.qty(), "overfill");
                    pf.push_order(terminated);
                }
            },
            // Position still moved, we just have no order to attribute it to.
            None => tracing::warn!(order_id = ?fill.order_id(), "fill for unknown order"),
        }
    }

    fn desired_orders_qty(&self, orders: &[Order<New>]) -> i64 {
        orders
            .iter()
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
    fn send_desired_orders<S: EventSource, R: Rms>(
        &mut self,
        desired: &HashMap<Instrument, Desired>,
        pf: &Portfolio,
        rms: &R,
        sink: &mut S,
    ) {
        for instrument_desired in desired.values() {
            for order in instrument_desired.des_ords() {
                let order = *order;
                let id = &order.order_id();

                if self.unacked.contains_key(id) || self.working.contains_key(id) {
                    continue;
                }
                if !rms.approve_order(&order, pf) {
                    continue;
                }

                tracing::debug!(order_id = ?id, side = ?order.side(), qty = %order.quantity().qty(), "send desired order");
                self.unacked.insert(*id, order); // Add to OMS state
                sink.submit(Request::SendOrder(order)); // OMS -> Executor
            }
        }
    }

    /// Sends market orders.
    ///
    /// Must be called the last:
    ///     **all manipulations with desired state and OMS state must be done before this.**
    fn send_market_orders<S: EventSource, R: Rms>(
        &mut self,
        desired: &HashMap<Instrument, Desired>,
        pf: &Portfolio,
        rms: &R,
        sink: &mut S,
    ) {
        for (instr, want) in desired {
            // Clamp the level, not the delta: clamping `m` would creep past the limit each pass.
            let dp = rms.clamp_position(instr, *want.dp(), pf).as_i64();
            let do_q = self.desired_orders_qty(want.des_ords());
            let wo = self.leaves_qty(instr);
            let rp = pf.position(instr).as_i64();
            let m = dp + do_q - wo - rp;
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
            tracing::info!(
                order_id = ?order.order_id(),
                instrument = %instr,
                side = ?side,
                qty = %order.quantity().qty(),
                dp = %Quantity::display_raw(dp),
                do_q = %Quantity::display_raw(do_q),
                wo = %Quantity::display_raw(wo),
                rp = %Quantity::display_raw(rp),
                m = %Quantity::display_raw(m),
                "send market order"
            );
            self.unacked.insert(order.order_id(), order);
            sink.submit(Request::SendOrder(order)); // OMS -> Executor
        }
    }

    /// Compare desired state to actual state and send orders to close the gap.
    pub fn reconcile<S: EventSource, R: Rms>(
        &mut self,
        desired: &HashMap<Instrument, Desired>,
        pf: &Portfolio,
        rms: &R,
        sink: &mut S,
    ) {
        if !rms.trading_allowed(pf) {
            return;
        }
        self.cancel_undesired(desired, sink);
        self.send_desired_orders(desired, pf, rms, sink);

        // MUST BE CALLED LAST
        self.send_market_orders(desired, pf, rms, sink);
    }

    fn cancel_undesired<S: EventSource>(
        &mut self,
        desired: &HashMap<Instrument, Desired>,
        sink: &mut S,
    ) {
        // all desired orders
        let wanted: HashSet<OrderId> = desired
            .values()
            .flat_map(|d| d.des_ords().iter().map(|o| o.order_id()))
            .collect();

        // all unack+working orders
        let live = self
            .unacked
            .values()
            .map(|o| (o.order_id(), *o.order_type()))
            .chain(
                self.working
                    .values()
                    .map(|o| (o.order_id(), *o.order_type())),
            );

        for (id, ty) in live.collect::<Vec<_>>() {
            // Market orders are never desired. Skip or we cancel them.
            if ty == OrderType::Market || wanted.contains(&id) || !self.pending_cancels.insert(id) {
                continue;
            }
            sink.submit(Request::CancelOrder(id));
        }
    }

    fn on_cancel_response(&mut self, id: &OrderId, success: &bool, pf: &mut Portfolio) {
        if !self.pending_cancels.contains(id) {
            tracing::warn!(id=?id, succ=?success, "cancel response not found in working cancels");
            return;
        };
        if !success {
            tracing::warn!(id=?id, succ=?success, "cancel response failed");
            return;
        }
        // We have already checked that it's there and cancel is successful
        let _ = self.pending_cancels.remove(id);

        // Now we need to get rid of that order in unacked or working
        let order = self
            .unacked
            .remove(id)
            .map(Order::into_working)
            // If order was in working
            .or_else(|| self.working.remove(id));

        match order {
            Some(working) => pf.push_order(working.into_cancelled()),
            None => {
                tracing::warn!(id=?id, "could not find order for a successful cancel");
            }
        }
    }
}
