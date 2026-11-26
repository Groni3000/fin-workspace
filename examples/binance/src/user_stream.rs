//! User data stream messages (the WebSocket API's signed subscription) into execution events.
//!
//! The stream reports every order of the account, whoever placed it, and its balances:
//!
//! ```text
//! {"subscriptionId":0,"event":{"e":"executionReport","s":"BTCUSDT","c":"<client id>","x":"TRADE",…}}
//! {"subscriptionId":0,"event":{"e":"outboundAccountPosition",…}}
//! {"id":"…","status":200,"result":{"subscriptionId":0},…}
//! ```
//!
//! An order Binance turns down at the request (a filter, the balance) never shows up here.

use std::fmt::{self, Display};

use jiff::Timestamp;
use oms::OrderId;
use oms::fill::Fill;
use oms::protocol::{ExecEvent, RejectReason};
use serde::Deserialize;
use tradeprim::Side;
use tradeprim::decimal::ParseDecimalError;
use tradeprim::position::NonZeroQuantity;
use tradeprim::price::Price;
use tradeprim::quantity::Quantity;

use crate::instruments;

#[derive(Debug)]
pub enum Update {
    /// One of our orders was accepted (`NEW`), turned down (`REJECTED`) or expired (`EXPIRED`).
    Exec(ExecEvent),
    /// One of our orders traded. The fee is not part of the fill: paid in BNB, it leaves the
    /// position alone; taken from the bought asset, it doesn't.
    Fill { fill: Fill, fee: Fee },
    /// An order that isn't ours: its client id is not an [`OrderId`] (placed in Binance's app,
    /// say).
    Foreign { client_id: String },
    /// Anything else: balances, replies to requests.
    Other,
}

/// A trade's fee, as Binance wrote it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fee {
    pub amount: String,
    pub asset: String,
}

#[derive(Debug)]
pub enum ParseError {
    Json(serde_json::Error),
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
    /// A field that parses but makes no sense: an unknown side, a trade of nothing.
    Invalid {
        field: &'static str,
        value: String,
    },
    /// An execution type we don't turn into an event yet (`CANCELED`, `TRADE_PREVENTION`, …).
    Unhandled {
        execution: String,
        client_id: String,
    },
}

impl Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Json(e) => write!(f, "invalid JSON: {e}"),
            ParseError::UnknownSymbol(s) => write!(f, "symbol {s} is not listed"),
            ParseError::Decimal {
                field,
                value,
                error,
            } => write!(f, "field {field}: {value:?}: {error}"),
            ParseError::Time { field, millis } => {
                write!(f, "field {field}: {millis} ms is not a valid time")
            }
            ParseError::Invalid { field, value } => write!(f, "field {field}: {value:?}"),
            ParseError::Unhandled {
                execution,
                client_id,
            } => write!(
                f,
                "execution type {execution} of order {client_id} is not handled"
            ),
        }
    }
}

impl std::error::Error for ParseError {}

#[derive(Deserialize)]
struct Envelope {
    event: Option<Event>,
}

#[derive(Deserialize)]
#[serde(tag = "e")]
enum Event {
    #[serde(rename = "executionReport")]
    Execution(Box<Report>),
    #[serde(other)]
    Other,
}

#[derive(Deserialize)]
struct Report {
    s: String,
    /// The client order id.
    c: String,
    #[serde(rename = "S")]
    side: String,
    /// The execution type: what just happened.
    x: String,
    /// The reject reason, `NONE` unless rejected.
    r: String,
    /// The last trade's quantity.
    l: String,
    /// The last trade's price.
    #[serde(rename = "L")]
    last_price: String,
    /// The last trade's fee.
    n: String,
    /// The fee's asset, `null` until the order trades.
    #[serde(rename = "N")]
    fee_asset: Option<String>,
    /// The transaction time.
    #[serde(rename = "T")]
    time: i64,
}

/// Parses one message. Instruments come from [`instruments::by_symbol`].
pub fn parse(raw: &str) -> Result<Update, ParseError> {
    let envelope: Envelope = serde_json::from_str(raw).map_err(ParseError::Json)?;
    match envelope.event {
        Some(Event::Execution(report)) => execution(*report),
        Some(Event::Other) | None => Ok(Update::Other),
    }
}

fn execution(r: Report) -> Result<Update, ParseError> {
    let Ok(order_id) = r.c.parse::<OrderId>() else {
        return Ok(Update::Foreign { client_id: r.c });
    };
    let listed = instruments::by_symbol(&r.s).ok_or(ParseError::UnknownSymbol(r.s))?;
    let event = match r.x.as_str() {
        "NEW" => ExecEvent::Ack(order_id),
        "REJECTED" => ExecEvent::Reject(order_id, RejectReason::Venue(r.r)),
        "EXPIRED" => ExecEvent::Expired(listed.instrument, order_id),
        "TRADE" => {
            let side = match r.side.as_str() {
                "BUY" => Side::Buy,
                "SELL" => Side::Sell,
                _ => return Err(invalid("S", r.side)),
            };
            let quantity: Quantity = decimal("l", &r.l)?;
            let quantity = NonZeroQuantity::new(quantity).ok_or_else(|| invalid("l", r.l))?;
            let fill = Fill::new(
                order_id,
                time("T", r.time)?,
                listed.instrument,
                side,
                quantity,
                decimal::<Price>("L", &r.last_price)?,
            );
            let asset = r
                .fee_asset
                .ok_or_else(|| invalid("N", "null".to_string()))?;
            let fee = Fee { amount: r.n, asset };
            return Ok(Update::Fill { fill, fee });
        }
        _ => {
            return Err(ParseError::Unhandled {
                execution: r.x,
                client_id: r.c,
            });
        }
    };
    Ok(Update::Exec(event))
}

fn invalid(field: &'static str, value: String) -> ParseError {
    ParseError::Invalid { field, value }
}

fn decimal<D: std::str::FromStr<Err = ParseDecimalError>>(
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
    use super::*;

    /// The recorded fill of a demo buy (`tests/fixtures/demo-user_stream-round_trip.jsonl`).
    const TRADE: &str = r#"{"subscriptionId":0,"event":{"e":"executionReport","E":1795711130230,"s":"BTCUSDT","c":"01a218b9-59f3-763a-8883-00e35b195ca4","S":"BUY","o":"MARKET","f":"GTC","q":"0.00010000","p":"0.00000000","P":"0.00000000","F":"0.00000000","g":-1,"C":"","x":"TRADE","X":"FILLED","r":"NONE","i":86468151613,"l":"0.00010000","z":"0.00010000","L":"60440.01000000","n":"0.00000010","N":"BTC","T":1795711130230,"t":356323120,"I":173852403415,"w":false,"m":false,"M":true,"O":1795711130230,"Z":"6.04400100","Y":"6.04400100","Q":"0.00000000","W":1795711130230,"V":"EXPIRE_MAKER"}}"#;
    const ID: &str = "01a218b9-59f3-763a-8883-00e35b195ca4";

    fn id() -> OrderId {
        ID.parse().expect("a UUID")
    }

    fn with_execution(x: &str) -> String {
        TRADE
            .replace(r#""x":"TRADE""#, &format!(r#""x":"{x}""#))
            .replace(r#""l":"0.00010000""#, r#""l":"0.00000000""#)
    }

    #[test]
    fn a_trade_is_a_fill_with_its_fee() {
        let Update::Fill { fill, fee } = parse(TRADE).expect("parses") else {
            panic!("expected a fill");
        };
        assert_eq!(
            fill,
            Fill::new(
                id(),
                Timestamp::from_millisecond(1_795_711_130_230).unwrap(),
                instruments::btc_usdt().instrument,
                Side::Buy,
                NonZeroQuantity::new("0.0001".parse().unwrap()).unwrap(),
                Price::from_str_unchecked("60440.01"),
            )
        );
        assert_eq!(
            fee,
            Fee {
                amount: "0.00000010".to_string(),
                asset: "BTC".to_string()
            }
        );
    }

    #[test]
    fn a_partial_fill_is_the_last_trade_only() {
        let raw = TRADE
            .replace(r#""l":"0.00010000""#, r#""l":"0.00004000""#)
            .replace(r#""X":"FILLED""#, r#""X":"PARTIALLY_FILLED""#);
        let Update::Fill { fill, .. } = parse(&raw).expect("parses") else {
            panic!("expected a fill");
        };
        assert_eq!(fill.quantity().qty().to_string(), "0.00004");
    }

    #[test]
    fn a_rejection_keeps_binances_reason() {
        let raw =
            with_execution("REJECTED").replace(r#""r":"NONE""#, r#""r":"INSUFFICIENT_BALANCES""#);
        let update = parse(&raw).expect("parses");
        assert!(
            matches!(&update, Update::Exec(ExecEvent::Reject(o, RejectReason::Venue(r))) if *o == id() && r == "INSUFFICIENT_BALANCES"),
            "{update:?}"
        );
    }

    #[test]
    fn an_expiry_names_the_instrument() {
        let update = parse(&with_execution("EXPIRED")).expect("parses");
        assert!(
            matches!(&update, Update::Exec(ExecEvent::Expired(i, o)) if *i == instruments::btc_usdt().instrument && *o == id()),
            "{update:?}"
        );
    }

    #[test]
    fn an_order_placed_elsewhere_is_foreign() {
        let raw = TRADE.replace(ID, "web_3f1c0a");
        let update = parse(&raw).expect("parses");
        assert!(
            matches!(&update, Update::Foreign { client_id } if client_id == "web_3f1c0a"),
            "{update:?}"
        );
    }

    #[test]
    fn an_unhandled_execution_type_is_an_error() {
        let error = parse(&with_execution("CANCELED")).expect_err("not handled");
        assert_eq!(
            error.to_string(),
            "execution type CANCELED of order 01a218b9-59f3-763a-8883-00e35b195ca4 is not handled"
        );
    }

    #[test]
    fn a_trade_of_nothing_is_invalid() {
        let raw = TRADE.replace(r#""l":"0.00010000""#, r#""l":"0.00000000""#);
        let error = parse(&raw).expect_err("invalid");
        assert_eq!(error.to_string(), r#"field l: "0.00000000""#);
    }

    #[test]
    fn replies_are_other() {
        let raw = r#"{"id":"0949832961fa8b5453414cce57c21e33","status":200,"result":{"subscriptionId":0},"rateLimits":[]}"#;
        assert!(matches!(parse(raw).expect("parses"), Update::Other));
    }
}
