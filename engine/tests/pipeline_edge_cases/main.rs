//! The whole pipeline (strategy, OMS, RMS, `event_loop::run`) in the cases the examples don't
//! cover, one folder per simulated executor. Each case pins one trace: the events the
//! strategy saw, the requests the OMS sent and the warnings logged, in order.

mod common;

mod market_executor;
mod mkt_stp_lmt_executor;
mod unacked_cancel_refused;
