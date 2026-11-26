//! The kline parser on recorded messages: 16 lines of `record demo btcusdt`.

use binance_example::kline::{Message, parse};
use mdata::{Candle, HasTimestamp, HasVolume};
use tradeprim::price::Price;
use tradeprim::volume::Volume;

const FIXTURE: &str = include_str!("fixtures/demo-BTCUSDT-kline_1s.tsv");

#[test]
fn every_recorded_message_parses() {
    let mut replies = 0;
    let mut klines = Vec::new();
    for line in FIXTURE.lines() {
        let mut fields = line.splitn(3, '\t');
        let (_received, kind, payload) = (fields.next(), fields.next(), fields.next());
        if kind != Some("message") {
            continue;
        }
        match parse(payload.expect("a payload")).expect("parses") {
            Message::Kline(k) => klines.push(k),
            Message::Reply { error, .. } => {
                assert_eq!(error, None);
                replies += 1;
            }
        }
    }
    assert_eq!(replies, 1, "the SUBSCRIBE reply");
    assert_eq!(klines.len(), 14);
    assert!(klines.iter().all(|k| k.closed));

    // One candle per second, back to back.
    let starts: Vec<i64> = klines
        .iter()
        .map(|k| k.candle.timestamp().as_millisecond())
        .collect();
    assert_eq!(starts.first(), Some(&1_795_657_566_000));
    assert!(starts.windows(2).all(|w| w[1] - w[0] == 1000), "{starts:?}");

    let first = &klines[0].candle;
    assert_eq!(first.open(), Price::from_str_unchecked("60731.96"));
    assert_eq!(first.close(), Price::from_str_unchecked("60731.95"));
    let total: Volume = klines.iter().map(|k| k.candle.volume()).sum();
    assert_eq!(total.to_string(), "1.07135");
}
