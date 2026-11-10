use uuid::Uuid;

pub mod desired;
pub mod fill;
pub mod manager;
pub mod order;
pub mod portfolio;
pub mod protocol;
pub mod rms;

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
