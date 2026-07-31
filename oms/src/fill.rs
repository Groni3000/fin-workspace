use chrono::{DateTime, Utc};
use instrid::instruments::Instrument;
use tradeprim::{Side, price::Price, quantity::Quantity};
use uuid::Uuid;

/// Fill representation.
///
pub struct Fill {
    order_id: Uuid,
    timestamp: DateTime<Utc>,
    instrument: Instrument,
    side: Side,
    quantity: Quantity,
    price: Price,
}

impl Fill {
    pub fn new(
        order_id: Uuid,
        timestamp: DateTime<Utc>,
        instrument: Instrument,
        side: Side,
        quantity: Quantity,
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

    pub fn quantity(&self) -> Quantity {
        self.quantity
    }

    pub fn price(&self) -> Price {
        self.price
    }

    pub fn order_id(&self) -> Uuid {
        self.order_id
    }
}

/*
let ts = Timestamp::from_unix(
    NoContext,
    timestamp.timestamp() as u64,
    timestamp.timestamp_subsec_nanos(),
);

Uuid::new_v7(ts)
*/
