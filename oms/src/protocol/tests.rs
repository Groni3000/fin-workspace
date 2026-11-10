use chrono::DateTime;
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use tradeprim::{Side, currency::Currency, price::Price, quantity::Quantity};

use super::{ExecEvent, RejectReason};
use crate::{
    fill::Fill,
    order::{OrderBuilder, OrderType},
};

fn spy() -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new("SPY", AssetClass::Equity).expect("valid asset"),
        Asset::new("USD", AssetClass::Currency).expect("valid asset"),
        Mic::arcx(),
        Currency::usd(),
    ))
}

#[test]
fn every_exec_event_names_its_order() {
    let qty = Quantity::from_str_unchecked("1")
        .non_zero()
        .expect("non-zero quantity");
    let order = OrderBuilder::new(spy(), Side::Buy, qty)
        .verify()
        .expect("a valid order")
        .build();
    let id = order.order_id();
    let fill = Fill::new(
        id,
        DateTime::from_timestamp_nanos(0),
        spy(),
        Side::Buy,
        qty,
        Price::from_str_unchecked("100"),
    );

    let events = [
        ExecEvent::Ack(id),
        ExecEvent::Fill(fill),
        ExecEvent::Reject(id, RejectReason::UnsupportedOrderType(OrderType::Market)),
        ExecEvent::CancelResponse(id, true),
        ExecEvent::Expired(spy(), id),
    ];

    for event in &events {
        assert_eq!(event.order_id(), id, "{event:?}");
    }
}
