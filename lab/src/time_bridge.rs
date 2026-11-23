//! Conversions between `chrono`, which lab's time-zone code still uses, and `jiff`, the
//! timestamp type of the records.

use chrono::{DateTime, Utc};
use jiff::Timestamp;

pub(crate) fn to_jiff(ts: DateTime<Utc>) -> Timestamp {
    let nanos = ts
        .timestamp_nanos_opt()
        .expect("timestamp within the i64-nanosecond range");
    Timestamp::from_nanosecond(nanos.into()).expect("i64 nanoseconds are in range")
}

pub(crate) fn to_chrono(ts: Timestamp) -> DateTime<Utc> {
    let nanos =
        i64::try_from(ts.as_nanosecond()).expect("timestamp within the i64-nanosecond range");
    DateTime::from_timestamp_nanos(nanos)
}
