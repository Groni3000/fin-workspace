use instrid::{
    asset::{Asset, AssetClass},
    instruments::{Instrument, Stock},
    mic::Mic,
};
use jiff::Timestamp;
use tradeprim::{
    Side, currency::Currency, position::NonZeroQuantity, price::Price, quantity::Quantity,
};

use super::{MaxPositionRms, Rms};
use crate::{
    fill::Fill,
    order::{New, Order, OrderBuilder},
    portfolio::Portfolio,
};

fn spy() -> Instrument {
    Instrument::Stock(Stock::new(
        Asset::new("SPY", AssetClass::Equity).expect("valid asset"),
        Asset::new("USD", AssetClass::Currency).expect("valid asset"),
        Mic::arcx(),
        Currency::usd(),
    ))
}

fn qty(n: &str) -> NonZeroQuantity {
    Quantity::from_str_unchecked(n)
        .non_zero()
        .expect("non-zero quantity")
}

fn market(side: Side, n: &str) -> Order<New> {
    OrderBuilder::new(spy(), side, qty(n))
        .verify()
        .expect("a market order needs nothing else")
        .build()
}

/// A portfolio holding `n` signed lots.
fn holding(n: i64) -> Portfolio {
    let mut pf = Portfolio::new();
    if n != 0 {
        let side = if n > 0 { Side::Buy } else { Side::Sell };
        let order = market(side, &n.abs().to_string());
        pf.push_fill(Fill::new(
            order.order_id(),
            Timestamp::UNIX_EPOCH,
            spy(),
            side,
            qty(&n.abs().to_string()),
            Price::from_str_unchecked("100"),
        ));
    }
    pf
}

#[test]
fn a_cap_judges_the_position_an_order_leads_to_not_its_size() {
    let rms = MaxPositionRms::new(qty("1"));
    let cases = [
        // held, side, quantity, approved
        (0, Side::Buy, "1", true),    // flat → long 1: at the cap
        (0, Side::Sell, "1", true),   // flat → short 1: at the cap
        (0, Side::Buy, "2", false),   // flat → long 2
        (1, Side::Buy, "1", false),   // long 1 → long 2
        (1, Side::Sell, "1", true),   // long 1 → flat
        (1, Side::Sell, "2", true),   // long 1 → short 1: a reversal, order bigger than the cap
        (1, Side::Sell, "3", false),  // long 1 → short 2
        (-1, Side::Buy, "2", true),   // short 1 → long 1
        (-1, Side::Sell, "1", false), // short 1 → short 2
    ];
    for (held, side, n, approved) in cases {
        assert_eq!(
            rms.approve_order(&market(side, n), &holding(held)),
            approved,
            "held {held}, {side:?} {n}"
        );
    }
}
