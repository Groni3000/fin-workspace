use std::sync::{
    Arc,
    atomic::{AtomicI64, Ordering},
};

use chrono::DateTime;
use tracing_subscriber::{EnvFilter, fmt::format::Writer, fmt::time::FormatTime};

/// Timestamp source for log lines that reports *simulated* time.
#[derive(Debug, Clone, Default)]
pub struct SimClock(Arc<AtomicI64>);

impl SimClock {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&self, nanos: i64) {
        self.0.store(nanos, Ordering::Relaxed);
    }

    pub fn get(&self) -> i64 {
        self.0.load(Ordering::Relaxed)
    }
}

impl FormatTime for SimClock {
    fn format_time(&self, w: &mut Writer<'_>) -> std::fmt::Result {
        write!(w, "{}", DateTime::from_timestamp_nanos(self.get()))
    }
}

/// Human-readable logs stamped with simulated time. `RUST_LOG` overrides the default level.
pub fn init(clock: SimClock) {
    tracing_subscriber::fmt()
        .with_timer(clock)
        .with_target(false)
        .with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .init();
}

/// One JSON object per line.
pub fn init_json(clock: SimClock) {
    tracing_subscriber::fmt()
        .json()
        .with_timer(clock)
        .with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .init();
}
