use instrid::instruments::Instrument;
use oms::order::{New, Order};
use tradeprim::position::{NonZeroQuantity, Position};

use crate::portfolio::Portfolio;

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

/// Caps absolute position size per instrument and rejects oversized resting orders.
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
    fn clamp_position(&self, instrument: &Instrument, want: Position, _pf: &Portfolio) -> Position {
        let clamped = match want {
            Position::Flat => return Position::Flat,
            Position::Long(q) if q.value() > self.max_position.value() => {
                Position::Long(self.max_position)
            }
            Position::Short(q) if q.value() > self.max_position.value() => {
                Position::Short(self.max_position)
            }
            other => other,
        };
        if clamped != want {
            tracing::warn!(
                instrument = %instrument,
                %want,
                %clamped,
                max = %self.max_position.qty(),
                "rms clamped desired position"
            );
        }
        clamped
    }

    fn approve_order(&self, order: &Order<New>, _pf: &Portfolio) -> bool {
        let approved = order.quantity().value() <= self.max_position.value();
        if !approved {
            tracing::warn!(
                order_id = ?order.order_id(),
                quantity = %order.quantity().qty(),
                max = %self.max_position.qty(),
                "rms rejected desired order"
            );
        }
        approved
    }
}
