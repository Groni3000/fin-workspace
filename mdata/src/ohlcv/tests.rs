use chrono::{DateTime, Utc};
use tradeprim::{price::Price, volume::Volume};

use super::*;

fn at(minute: i64) -> DateTime<Utc> {
    DateTime::from_timestamp(minute * 60, 0).expect("valid timestamp")
}

fn candle(minute: i64, [o, h, l, c]: [&str; 4], volume: u64) -> Ohlcv {
    let p = Price::from_str_unchecked;
    Ohlcv::new(
        at(minute),
        p(o),
        p(h),
        p(l),
        p(c),
        Volume::from_units(volume),
    )
}

/// The second record sets a new high and low, the third sets neither: the candle keeps the
/// extremes, not the latest values.
#[test]
fn merge_keeps_open_and_extremes_takes_the_last_close_and_adds_volume() {
    let mut five_minutes = Ohlcv::seed(at(0), &candle(1, ["100", "101", "99", "100"], 3));
    five_minutes.merge(&candle(2, ["100", "104", "97", "103"], 5));
    five_minutes.merge(&candle(3, ["103", "103", "102", "102"], 2));

    assert_eq!(five_minutes, candle(0, ["100", "104", "97", "102"], 10));
}
