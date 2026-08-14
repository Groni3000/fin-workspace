pub mod market_only;

/// Marks type as an executor: it fills/cancels/rejects orders.
pub trait Executor {}
