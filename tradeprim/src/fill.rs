use crate::Amount;
use chrono::{DateTime, Utc};
use instrid::prelude::*;
use rust_decimal::Decimal;
use std::sync::Arc;

/// Represents a price of an asset.
///
/// Can be negative, zero, or positive.
#[derive(Debug)]
pub struct Price(Amount);

/// Represents a quantity of an asset.
///
/// A quantity is a positive, non-zero amount of an asset.
#[derive(Debug)]
pub struct Quantity(Amount);

#[derive(Debug)]
pub struct Fill {
    timestamp: DateTime<Utc>,
    instrument: Arc<Instrument>,
    quantity: Quantity,
    price: Price,
    fee: Option<Amount>,
}

impl Price {
    pub fn new(value: Decimal, asset: Asset) -> Self {
        Self(Amount::new(value, asset))
    }
}

impl Quantity {
    pub fn new(value: Decimal, asset: Asset) -> Option<Self> {
        match value.is_sign_positive() && !value.is_zero() {
            true => Some(Self(Amount::new(value, asset))),
            false => None,
        }
    }
}

impl Fill {
    pub fn new(
        timestamp: DateTime<Utc>,
        instrument: Arc<Instrument>,
        quantity: Quantity,
        price: Price,
        fee: Option<Amount>,
    ) -> Self {
        Self {
            timestamp,
            instrument,
            quantity,
            price,
            fee,
        }
    }

    pub fn from_raw(
        timestamp: DateTime<Utc>,
        instrument: Arc<Instrument>,
        quantity: Decimal,
        price: Decimal,
        fee: Option<Decimal>,
    ) -> Self {
        let base = instrument.base().clone();
        let quote = instrument.quote().clone();

        Self {
            timestamp,
            instrument,
            quantity: Quantity::new(quantity, base).unwrap(),
            price: Price::new(price, quote),
            fee: fee.map(|f| Amount::new(f, quote)),
        }
    }
}
