use crate::order::{New, Order};
use instrid::instruments::Instrument;
use tradeprim::position::{NonZeroQuantity, Position};

use crate::{EXEC_TARGET, portfolio::Portfolio};

/// Risk gate sitting between Strategy and OMS.
pub trait Rms {
    /// Global gate, checked once per reconcile pass before anything is sent.
    fn trading_allowed(&self, _pf: &Portfolio) -> bool {
        true
    }

    /// Clamp the desired position before the diff is computed.
    fn clamp_position(&self, instrument: &Instrument, want: Position, pf: &Portfolio) -> Position;

    /// Decide whether to approve an order.
    fn approve_order(&self, order: &Order<New>, pf: &Portfolio) -> bool;
}

/// Lets `Box<dyn Rms>` satisfy `R: Rms`, so the implementation can be picked at runtime.
impl<T: Rms + ?Sized> Rms for Box<T> {
    fn trading_allowed(&self, pf: &Portfolio) -> bool {
        (**self).trading_allowed(pf)
    }

    fn clamp_position(&self, instrument: &Instrument, want: Position, pf: &Portfolio) -> Position {
        (**self).clamp_position(instrument, want, pf)
    }

    fn approve_order(&self, order: &Order<New>, pf: &Portfolio) -> bool {
        (**self).approve_order(order, pf)
    }
}

/// Approves everything. The baseline.
#[derive(Debug, Default, Clone, Copy)]
pub struct NaiveRms;

impl Rms for NaiveRms {
    fn clamp_position(
        &self,
        _instrument: &Instrument,
        want: Position,
        _pf: &Portfolio,
    ) -> Position {
        want
    }

    fn approve_order(&self, _order: &Order<New>, _pf: &Portfolio) -> bool {
        true
    }
}

/// Rejects everything. Useful to "prove" everything's sound: no orders may leave.
#[derive(Debug, Default, Clone, Copy)]
pub struct HaltedRms;

impl Rms for HaltedRms {
    fn trading_allowed(&self, _pf: &Portfolio) -> bool {
        false
    }

    fn clamp_position(
        &self,
        _instrument: &Instrument,
        _want: Position,
        _pf: &Portfolio,
    ) -> Position {
        Position::Flat
    }

    fn approve_order(&self, _order: &Order<New>, _pf: &Portfolio) -> bool {
        false
    }
}

/// Caps the absolute position per instrument: clamps the wanted position, and refuses an order
/// that would take the position beyond the cap.
#[derive(Debug, Clone, Copy)]
pub struct MaxPositionRms {
    max_position: NonZeroQuantity,
}

impl MaxPositionRms {
    pub fn new(max_position: NonZeroQuantity) -> Self {
        Self { max_position }
    }

    pub fn max_position(&self) -> NonZeroQuantity {
        self.max_position
    }
}

impl Rms for MaxPositionRms {
    /// Logs nothing: it runs after every event, so a warning here would repeat on every one.
    /// The OMS logs the clamp on the order it shapes (`want` next to `dp` in "send market
    /// order").
    fn clamp_position(
        &self,
        _instrument: &Instrument,
        want: Position,
        _pf: &Portfolio,
    ) -> Position {
        match want {
            Position::Flat => Position::Flat,
            Position::Long(q) if q.value() > self.max_position.value() => {
                Position::Long(self.max_position)
            }
            Position::Short(q) if q.value() > self.max_position.value() => {
                Position::Short(self.max_position)
            }
            other => other,
        }
    }

    /// Judges the position the order leads to: what's held plus this order. Orders still in
    /// flight aren't visible here, so while one is unfilled a valid order may be refused; the
    /// OMS asks again on the next event.
    fn approve_order(&self, order: &Order<New>, pf: &Portfolio) -> bool {
        let held = pf.position(&order.instrument()).as_i64();
        let after = held + order.side().as_i64() * order.quantity().value() as i64;
        let approved = after.unsigned_abs() <= self.max_position.value();
        if !approved {
            tracing::warn!(target: EXEC_TARGET,
                order_id = ?order.order_id(),
                side = ?order.side(),
                quantity = %order.quantity().qty(),
                max = %self.max_position.qty(),
                "rms rejected order"
            );
        }
        approved
    }
}

#[cfg(test)]
mod tests;
