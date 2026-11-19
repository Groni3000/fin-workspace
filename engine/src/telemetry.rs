use std::sync::{
    Arc,
    atomic::{AtomicI64, Ordering},
};

mod weekly;

use std::{error::Error, path::Path};

use chrono::DateTime;
use oms::EXEC_TARGET;
use tracing_subscriber::{
    EnvFilter, Layer,
    filter::filter_fn,
    fmt::{self, format::Writer, time::FormatTime},
    layer::SubscriberExt,
    util::SubscriberInitExt,
};
use weekly::WeeklyFile;

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

/// Sends all logging to two files in `dir`, the same for backtests and live runs:
///
/// - `{prefix}.exec.<date>.log`: the execution log. Every order-lifecycle line (target
///   [`oms::EXEC_TARGET`]) and nothing else, one JSON object per line, whatever `RUST_LOG` says.
/// - `{prefix}.diag.<date>.log`: the diagnostics log. Every other line, human-readable.
///   `RUST_LOG` sets its level (default `info`).
///
/// Both files start over every week, on Sunday at 00:00 UTC (wall clock); `<date>` is that
/// Sunday. Old files are never deleted. Lines are stamped with `clock`'s time. Writes block, so a line is on disk once the
/// macro returns: nothing is lost if the process dies.
///
/// Give each process its own `prefix` (or `dir`): two processes writing to the same file
/// interleave or fail, on Windows especially.
///
/// Fails if `dir` can't be created or a global subscriber is already set.
pub fn init(
    clock: SimClock,
    dir: impl AsRef<Path>,
    prefix: &str,
) -> Result<(), Box<dyn Error + Send + Sync>> {
    let dir = dir.as_ref();
    let weekly = |name: &str| WeeklyFile::new(dir, &format!("{prefix}.{name}"));

    let exec = fmt::layer()
        .json()
        .with_timer(clock.clone())
        .with_writer(weekly("exec")?)
        .with_filter(filter_fn(|meta| meta.target() == EXEC_TARGET));
    let diag = fmt::layer()
        .with_timer(clock)
        .with_target(false)
        .with_ansi(false)
        .with_writer(weekly("diag")?)
        .with_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()))
        .with_filter(filter_fn(|meta| meta.target() != EXEC_TARGET));

    tracing_subscriber::registry()
        .with(exec)
        .with(diag)
        .try_init()?;
    Ok(())
}
