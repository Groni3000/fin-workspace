//! The whole pipeline (strategy, OMS, RMS, `event_loop::run`) in the cases the examples don't
//! cover, one folder per simulated executor. Each case pins one trace: the events the
//! strategy saw and the requests the OMS sent, in order.

mod common;

mod market_executor;
