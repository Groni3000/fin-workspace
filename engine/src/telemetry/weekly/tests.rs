use std::{fs, io::Write};

use jiff::{Timestamp, ToSpan, tz::TimeZone};
use tracing_subscriber::fmt::MakeWriter;

use super::{WeeklyFile, week_start};

/// Unix seconds of a UTC date and time, e.g. `"2026-11-14T23:59:59Z"`.
fn secs(utc: &str) -> i64 {
    utc.parse::<Timestamp>()
        .expect("a valid RFC 3339 time")
        .as_second()
}

/// Days since 1970-01-01 of a date, e.g. `"2026-11-15"`.
fn day(date: &str) -> i64 {
    secs(&format!("{date}T00:00:00Z")) / 86_400
}

#[test]
fn a_week_starts_on_sunday_at_midnight_utc() {
    // 2026-11-15 is a Sunday.
    assert_eq!(week_start(secs("2026-11-15T00:00:00Z")), day("2026-11-15"));
    assert_eq!(week_start(secs("2026-11-21T23:59:59Z")), day("2026-11-15"));
    assert_eq!(week_start(secs("2026-11-14T23:59:59Z")), day("2026-11-08"));
}

/// A new file starts on Sunday, and a restart in the same week appends to this week's file
/// instead of overwriting it.
#[test]
fn files_start_on_sunday_and_are_only_ever_appended_to() {
    let dir = std::env::temp_dir().join(format!("engine-weekly-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    let line = |file: &WeeklyFile, utc: &str, text: &str| {
        file.writer_at(secs(utc))
            .write_all(format!("{text}\n").as_bytes())
            .expect("written");
    };

    let file = WeeklyFile::open_at(&dir, "x", secs("2026-11-14T23:59:59Z")).expect("opened");
    line(&file, "2026-11-14T23:59:59Z", "saturday");
    line(&file, "2026-11-15T00:00:00Z", "sunday");
    drop(file);
    let restarted = WeeklyFile::open_at(&dir, "x", secs("2026-11-16T09:00:00Z")).expect("reopened");
    line(&restarted, "2026-11-16T09:00:00Z", "after restart");

    let mut names: Vec<_> = fs::read_dir(&dir)
        .expect("dir exists")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .into_string()
                .expect("utf-8")
        })
        .collect();
    names.sort();
    assert_eq!(names, ["x.2026-11-08.log", "x.2026-11-15.log"]);
    let read = |name: &str| fs::read_to_string(dir.join(name)).expect("readable");
    assert_eq!(read("x.2026-11-08.log"), "saturday\n");
    assert_eq!(read("x.2026-11-15.log"), "sunday\nafter restart\n");

    let _ = fs::remove_dir_all(&dir);
}

/// After weeks without a line, the next line goes to the file of the week it's written in,
/// not of the week after the last file. That holds for a process that kept running (the machine
/// slept) and for a restart after an outage. The weeks in between get no files.
#[test]
fn after_weeks_of_silence_the_current_weeks_file_starts() {
    let dir = std::env::temp_dir().join(format!("engine-weekly-gap-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    let line = |file: &WeeklyFile, utc: &str, text: &str| {
        file.writer_at(secs(utc))
            .write_all(format!("{text}\n").as_bytes())
            .expect("written");
    };

    let file = WeeklyFile::open_at(&dir, "x", secs("2026-11-14T12:00:00Z")).expect("opened");
    line(&file, "2026-11-14T12:00:00Z", "before the sleep");
    // Thursday, almost 3 weeks later.
    line(&file, "2026-12-03T08:00:00Z", "after the sleep");
    drop(file);
    // Down for another 2 weeks, then restarted on a Sunday afternoon.
    let restarted = WeeklyFile::open_at(&dir, "x", secs("2026-12-20T15:00:00Z")).expect("reopened");
    line(&restarted, "2026-12-20T15:00:00Z", "after the restart");

    let mut names: Vec<_> = fs::read_dir(&dir)
        .expect("dir exists")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .into_string()
                .expect("utf-8")
        })
        .collect();
    names.sort();
    assert_eq!(
        names,
        ["x.2026-11-08.log", "x.2026-11-29.log", "x.2026-12-20.log"]
    );
    let read = |name: &str| fs::read_to_string(dir.join(name)).expect("readable");
    assert_eq!(read("x.2026-11-08.log"), "before the sleep\n");
    assert_eq!(read("x.2026-11-29.log"), "after the sleep\n");
    assert_eq!(read("x.2026-12-20.log"), "after the restart\n");

    let _ = fs::remove_dir_all(&dir);
}

/// The date of the Sunday that started the current wall-clock week, worked out with `jiff`
/// rather than with `week_start`.
fn this_weeks_sunday() -> String {
    let today = Timestamp::now().to_zoned_datetime(TimeZone::UTC).date();
    let sunday = today - today.weekday().to_sunday_zero_offset().days();
    sunday.to_string()
}

/// What `init` actually uses: `new` and `make_writer`, both on the wall clock. `new` opens this
/// week's file, and `make_writer` follows the wall clock forward.
#[test]
fn new_and_make_writer_write_to_the_current_wall_clock_weeks_file() {
    let dir = std::env::temp_dir().join(format!("engine-weekly-wall-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);

    let before = this_weeks_sunday();
    let file = WeeklyFile::new(&dir, "x").expect("opened");
    file.make_writer().write_all(b"now\n").expect("written");
    let after = this_weeks_sunday();

    let names: Vec<_> = fs::read_dir(&dir)
        .expect("dir exists")
        .map(|entry| {
            entry
                .expect("entry")
                .file_name()
                .into_string()
                .expect("utf-8")
        })
        .collect();
    // Run across Sunday 00:00 UTC, the file may belong to either week.
    let expected = [format!("x.{before}.log"), format!("x.{after}.log")];
    assert!(
        names.len() == 1 && expected.contains(&names[0]),
        "{names:?}, expected one of {expected:?}"
    );
    assert_eq!(
        fs::read_to_string(dir.join(&names[0])).expect("readable"),
        "now\n"
    );

    // Opened as of a week ago, `make_writer` must still move on to this week's file: a
    // `make_writer` stuck in the past would keep writing to last week's.
    let week_ago = Timestamp::now().as_second() - 7 * 86_400;
    let file = WeeklyFile::open_at(&dir, "y", week_ago).expect("opened");
    file.make_writer()
        .write_all(b"moved on\n")
        .expect("written");
    let after = this_weeks_sunday();
    let expected = [format!("y.{before}.log"), format!("y.{after}.log")];
    let current = expected
        .iter()
        .find(|name| dir.join(name).exists())
        .unwrap_or_else(|| panic!("none of {expected:?} exists"));
    assert_eq!(
        fs::read_to_string(dir.join(current)).expect("readable"),
        "moved on\n"
    );

    let _ = fs::remove_dir_all(&dir);
}
