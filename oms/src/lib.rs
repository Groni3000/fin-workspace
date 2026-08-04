use uuid::Uuid;

pub mod fill;
pub mod order;

pub mod prelude {
    pub use crate::OrderId;
    pub use crate::fill::Fill;
    pub use crate::order::{
        FillOutcome, New, Order, OrderBuilder, OrderBuilderError, OrderType, Terminated,
        TerminationReason, TimeInForce, Working,
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OrderId(Uuid);
