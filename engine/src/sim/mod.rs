//! Everything that only exists for backtests: the event queue and the simulated executors.
//!
//! Each simulated executor *should be* a superset of the previous one. Most of the code
//! *should be* copy-pasted. It's a sign of success, not a bad design.
//!
//! Once I'm confident enough that those executors are basically supersets of previous,
//! more simple ones, I can entirely drop predecessors or leave them as is because they
//! may flag more clearly strategy intention to the user.

mod market_only;
mod mkt_stp_lmt;
mod queue;

pub use market_only::MarketExecutor;
pub use mkt_stp_lmt::MarketStopLimitExecutor;
pub use queue::SimQueue;
