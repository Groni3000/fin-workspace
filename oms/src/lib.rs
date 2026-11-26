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

/// The `tracing` target of every order-lifecycle line: sent, acked, filled, rejected,
/// cancelled, expired, or blocked by the RMS. `engine::telemetry` writes these lines to the
/// execution log and keeps them out of the diagnostics log.
///
/// Code outside this crate that logs order-lifecycle lines must use it too:
/// `tracing::info!(target: oms::EXEC_TARGET, ...)`.
pub const EXEC_TARGET: &str = "exec";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OrderId(Uuid);

impl std::str::FromStr for OrderId {
    type Err = uuid::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Uuid::try_parse(s).map(Self)
    }
}
