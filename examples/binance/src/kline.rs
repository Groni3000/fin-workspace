//! Kline stream messages (`<symbol>@kline_<interval>` on the combined stream) into candles.
//!
//! A message is either a candle or the reply to one of our requests (`SUBSCRIBE`):
//!
//! ```text
//! {"stream":"btcusdt@kline_1s","data":{"e":"kline","E":…,"s":"BTCUSDT","k":{"t":…,"o":"…",…}}}
//! {"result":null,"id":"67dc…"}
//! ```

use std::fmt::{self, Display};
use std::str::FromStr;

use jiff::Timestamp;
use mdata::Tagged;
use mdata::ohlcv::Ohlcv;
use serde::Deserialize;
use tradeprim::decimal::ParseDecimalError;

use crate::instruments;

/// A candle as the stream reports it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Kline {
    /// Starts at the candle's open time.
    pub candle: Tagged<Ohlcv>,
    /// The candle's last millisecond (`T`).
    pub close_time: Timestamp,
    /// When Binance sent the message (`E`).
    pub event_time: Timestamp,
    /// `false` while the candle is still open. 1-second candles only arrive closed.
    pub closed: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Message {
    Kline(Kline),
    /// The reply to a request we sent, with Binance's error if it refused it.
    Reply {
        id: String,
        error: Option<String>,
    },
}

#[derive(Debug)]
pub enum ParseError {
    Json(serde_json::Error),
    /// Neither a candle nor a reply.
    Unexpected,
    /// The symbol isn't in [`instruments`].
    UnknownSymbol(String),
    Decimal {
        field: &'static str,
        value: String,
        error: ParseDecimalError,
    },
    Time {
        field: &'static str,
        millis: i64,
    },
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Json(e) => write!(f, "invalid JSON: {e}"),
            ParseError::Unexpected => write!(f, "neither a kline nor a reply"),
            ParseError::UnknownSymbol(s) => write!(f, "symbol {s} is not listed"),
            ParseError::Decimal {
                field,
                value,
                error,
            } => write!(f, "field {field}: {value:?}: {error}"),
            ParseError::Time { field, millis } => {
                write!(f, "field {field}: {millis} ms is not a valid time")
            }
        }
    }
}

impl std::error::Error for ParseError {}

#[derive(Deserialize)]
struct Envelope {
    data: Option<Event>,
    id: Option<String>,
    error: Option<serde_json::Value>,
}

#[derive(Deserialize)]
struct Event {
    #[serde(rename = "E")]
    event_time: i64,
    k: RawKline,
}

#[derive(Deserialize)]
struct RawKline {
    t: i64,
    #[serde(rename = "T")]
    close_time: i64,
    s: String,
    o: String,
    h: String,
    l: String,
    c: String,
    v: String,
    x: bool,
}

/// Parses one message. The candle's instrument comes from [`instruments::by_symbol`].
pub fn parse(raw: &str) -> Result<Message, ParseError> {
    let envelope: Envelope = serde_json::from_str(raw).map_err(ParseError::Json)?;
    if let Some(event) = envelope.data {
        return kline(event).map(Message::Kline);
    }
    match envelope.id {
        Some(id) => Ok(Message::Reply {
            id,
            error: envelope.error.map(|e| e.to_string()),
        }),
        None => Err(ParseError::Unexpected),
    }
}

fn kline(event: Event) -> Result<Kline, ParseError> {
    let k = event.k;
    let listed = instruments::by_symbol(&k.s).ok_or(ParseError::UnknownSymbol(k.s))?;
    let ohlcv = Ohlcv::new(
        time("t", k.t)?,
        decimal("o", &k.o)?,
        decimal("h", &k.h)?,
        decimal("l", &k.l)?,
        decimal("c", &k.c)?,
        decimal("v", &k.v)?,
    );
    Ok(Kline {
        candle: Tagged::new(listed.instrument, ohlcv),
        close_time: time("T", k.close_time)?,
        event_time: time("E", event.event_time)?,
        closed: k.x,
    })
}

fn decimal<D: FromStr<Err = ParseDecimalError>>(
    field: &'static str,
    value: &str,
) -> Result<D, ParseError> {
    value.parse().map_err(|error| ParseError::Decimal {
        field,
        value: value.to_string(),
        error,
    })
}

fn time(field: &'static str, millis: i64) -> Result<Timestamp, ParseError> {
    Timestamp::from_millisecond(millis).map_err(|_| ParseError::Time { field, millis })
}

#[cfg(test)]
mod tests {
    use mdata::{Candle, HasInstrument, HasTimestamp, HasVolume};

    use tradeprim::price::Price;

    use super::*;

    const EMPTY_SECOND: &str = r#"{"stream":"btcusdt@kline_1s","data":{"e":"kline","E":1795657567024,"s":"BTCUSDT","k":{"t":1795657565000,"T":1795657565999,"s":"BTCUSDT","i":"1s","f":-1,"L":-1,"o":"60760.01000000","c":"60760.01000000","h":"60760.01000000","l":"60760.01000000","v":"0.00000000","n":0,"x":true,"q":"0.00000000","V":"0.00000000","Q":"0.00000000","B":"0"}}}"#;

    fn price(s: &str) -> Price {
        Price::from_str_unchecked(s)
    }

    fn kline_of(raw: &str) -> Kline {
        match parse(raw).expect("parses") {
            Message::Kline(k) => k,
            other => panic!("expected a kline, got {other:?}"),
        }
    }

    #[test]
    fn a_candle_with_trades() {
        let raw = EMPTY_SECOND
            .replace(r#""o":"60760.01000000""#, r#""o":"60734.88000000""#)
            .replace(r#""h":"60760.01000000""#, r#""h":"60737.04000000""#)
            .replace(r#""l":"60760.01000000""#, r#""l":"60734.87000000""#)
            .replace(r#""c":"60760.01000000""#, r#""c":"60734.87000000""#)
            .replace(r#""v":"0.00000000""#, r#""v":"0.19257000""#);
        let k = kline_of(&raw);
        let c = k.candle;
        assert_eq!(c.instrument(), instruments::btc_usdt().instrument);
        assert_eq!(c.timestamp().to_string(), "2026-11-26T01:46:05Z");
        assert_eq!(
            (c.open(), c.high(), c.low(), c.close()),
            (
                price("60734.88"),
                price("60737.04"),
                price("60734.87"),
                price("60734.87")
            )
        );
        assert_eq!(c.volume().to_string(), "0.19257");
        assert_eq!(k.close_time.to_string(), "2026-11-26T01:46:05.999Z");
        assert_eq!(k.event_time.to_string(), "2026-11-26T01:46:07.024Z");
        assert!(k.closed);
    }

    /// No trades: the candle repeats the last price and its volume is zero.
    #[test]
    fn an_empty_second() {
        let c = kline_of(EMPTY_SECOND).candle;
        assert_eq!(c.open(), price("60760.01"));
        assert_eq!(c.close(), price("60760.01"));
        assert_eq!(c.volume().to_string(), "0");
    }

    /// Longer intervals send the candle while it's still open, too.
    #[test]
    fn an_open_candle() {
        assert!(!kline_of(&EMPTY_SECOND.replace(r#""x":true"#, r#""x":false"#)).closed);
    }

    #[test]
    fn a_reply() {
        assert_eq!(
            parse(r#"{"result":null,"id":"67dc850f"}"#).unwrap(),
            Message::Reply {
                id: "67dc850f".to_string(),
                error: None
            }
        );
        let refused = r#"{"error":{"code":2,"msg":"Invalid request"},"id":"7"}"#;
        assert_eq!(
            parse(refused).unwrap(),
            Message::Reply {
                id: "7".to_string(),
                error: Some(r#"{"code":2,"msg":"Invalid request"}"#.to_string())
            }
        );
    }

    #[test]
    fn an_unlisted_symbol_is_an_error() {
        let err = parse(&EMPTY_SECOND.replace(r#""s":"BTCUSDT","i""#, r#""s":"XRPUSDT","i""#))
            .unwrap_err();
        assert_eq!(err.to_string(), "symbol XRPUSDT is not listed");
    }

    #[test]
    fn a_bad_decimal_names_its_field() {
        let err =
            parse(&EMPTY_SECOND.replace(r#""h":"60760.01000000""#, r#""h":"6e4""#)).unwrap_err();
        assert!(err.to_string().starts_with(r#"field h: "6e4": "#), "{err}");
    }

    #[test]
    fn a_missing_field_is_an_error() {
        let err = parse(&EMPTY_SECOND.replace(r#""x":true,"#, "")).unwrap_err();
        assert!(err.to_string().contains("missing field `x`"), "{err}");
    }

    #[test]
    fn something_else_is_unexpected() {
        assert_eq!(
            parse(r#"{"stream":"btcusdt@kline_1s"}"#)
                .unwrap_err()
                .to_string(),
            "neither a kline nor a reply"
        );
    }
}
