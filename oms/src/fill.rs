use chrono::{DateTime, Utc};
use instrid::instruments::Instrument;
use tradeprim::{
    Side,
    position::{NonZeroQuantity, Position},
    price::Price,
};

use crate::OrderId;

/// Fill representation.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Fill {
    order_id: OrderId,
    timestamp: DateTime<Utc>,
    instrument: Instrument,
    side: Side,
    quantity: NonZeroQuantity,
    price: Price,
}

impl Fill {
    pub fn new(
        order_id: OrderId,
        timestamp: DateTime<Utc>,
        instrument: Instrument,
        side: Side,
        quantity: NonZeroQuantity,
        price: Price,
    ) -> Self {
        Self {
            order_id,
            timestamp,
            instrument,
            side,
            quantity,
            price,
        }
    }

    pub fn timestamp(&self) -> DateTime<Utc> {
        self.timestamp
    }

    pub fn instrument(&self) -> Instrument {
        self.instrument
    }

    pub fn side(&self) -> Side {
        self.side
    }

    pub fn quantity(&self) -> NonZeroQuantity {
        self.quantity
    }

    pub fn price(&self) -> Price {
        self.price
    }

    pub fn order_id(&self) -> OrderId {
        self.order_id
    }

    pub fn as_position(&self) -> Position {
        match self.side {
            Side::Buy => Position::Long(self.quantity),
            Side::Sell => Position::Short(self.quantity),
        }
    }
}
