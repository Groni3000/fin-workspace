//! A log file that starts over every week, on Sunday at 00:00 UTC (wall clock).

use std::{
    fs::{self, File, OpenOptions},
    io::{self, Write},
    path::{Path, PathBuf},
    sync::{Mutex, MutexGuard, PoisonError},
    time::{SystemTime, UNIX_EPOCH},
};

use chrono::DateTime;
use tracing_subscriber::fmt::MakeWriter;

const DAY: i64 = 86_400;

/// The Sunday that starts the week holding `secs` (Unix seconds, UTC), as days since 1970-01-01.
fn week_start(secs: i64) -> i64 {
    let day = secs.div_euclid(DAY);
    // 1970-01-01 was a Thursday, 4 days after a Sunday.
    day - (day + 4).rem_euclid(7)
}

fn wall_clock() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |since| since.as_secs() as i64)
}

/// Appends to `{dir}/{prefix}.<Sunday>.log`, where `<Sunday>` is the date the current week
/// started on, e.g. `strat_1.exec.2026-11-15.log`.
///
/// Writes are unbuffered and go straight to the file, one `write` per log line (that's how
/// `tracing-subscriber`'s `fmt` layer writes), under a lock, so lines don't interleave.
pub(crate) struct WeeklyFile {
    dir: PathBuf,
    prefix: String,
    open: Mutex<(i64, File)>,
}

impl WeeklyFile {
    /// Creates `dir` if needed and opens this week's file.
    pub(crate) fn new(dir: &Path, prefix: &str) -> io::Result<Self> {
        Self::open_at(dir, prefix, wall_clock())
    }

    /// [`Self::new`] at `now` (Unix seconds, UTC).
    fn open_at(dir: &Path, prefix: &str, now: i64) -> io::Result<Self> {
        fs::create_dir_all(dir)?;
        let week = week_start(now);
        let file = open_week(dir, prefix, week)?;
        Ok(Self {
            dir: dir.to_path_buf(),
            prefix: prefix.to_string(),
            open: Mutex::new((week, file)),
        })
    }

    /// The file for a line written at `now` (Unix seconds, UTC): the file of the week `now` is
    /// in, opened if it isn't the open one.
    fn writer_at(&self, now: i64) -> Current<'_> {
        let mut open = self.open.lock().unwrap_or_else(PoisonError::into_inner);
        let week = week_start(now);
        if week != open.0 {
            // If the new file can't be opened, keep writing to the old one: a line in last
            // week's file beats a lost line. The next line tries again.
            if let Ok(file) = open_week(&self.dir, &self.prefix, week) {
                *open = (week, file);
            }
        }
        Current(open)
    }
}

fn open_week(dir: &Path, prefix: &str, week: i64) -> io::Result<File> {
    let sunday = DateTime::from_timestamp(week * DAY, 0)
        .expect("a week start is a valid date")
        .date_naive();
    OpenOptions::new()
        .create(true)
        .append(true)
        .open(dir.join(format!("{prefix}.{sunday}.log")))
}

impl<'a> MakeWriter<'a> for WeeklyFile {
    type Writer = Current<'a>;

    fn make_writer(&'a self) -> Self::Writer {
        self.writer_at(wall_clock())
    }
}

/// The file of the current week, locked for one log line.
pub(crate) struct Current<'a>(MutexGuard<'a, (i64, File)>);

impl Write for Current<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.1.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.1.flush()
    }
}

#[cfg(test)]
mod tests;
