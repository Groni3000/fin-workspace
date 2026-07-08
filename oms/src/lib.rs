// use instrid::prelude::*;
// use std::{error::Error, fmt::Display, sync::Arc};

// #[derive(Debug, Clone)]
// pub struct Fill {
//     timestamp: DateTime<Utc>,
//     instrument: Arc<Instrument>,
//     quantity: Quantity,
//     side: Side,
//     price: Price,
//     fee: Option<Amount>,
// }

// impl Price {
//     pub fn new(value: Decimal, asset: Asset) -> Self {
//         Self(Amount::new(value, asset))
//     }
// }

// impl Quantity {
//     pub fn new(value: Decimal, asset: Asset) -> Option<Self> {
//         (value > Decimal::ZERO).then(|| Self(Amount::new(value, asset)))
//     }
// }

// /// Errors that can occur when creating a `Fill`.
// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
// pub enum FillError {
//     QuantityAssetMismatch { expected: Asset, got: Asset },
//     PriceAssetMismatch { expected: Asset, got: Asset },
//     FeeAssetMismatch { expected: Asset, got: Asset },
// }

// impl Display for FillError {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         std::fmt::Debug::fmt(self, f)
//     }
// }

// impl Error for FillError {}

// impl Fill {
//     /// Creates a [`Fill`](crate::fill::Fill). Validates [`Asset`](instrid::prelude::Asset)s
//     /// - instrument base asset is the same as the fill quantity asset.
//     /// - instrument quote asset is the same as the fill price asset and fee (if present).
//     pub fn new(
//         timestamp: DateTime<Utc>,
//         instrument: Arc<Instrument>,
//         quantity: Quantity,
//         side: Side,
//         price: Price,
//         fee: Option<Amount>,
//     ) -> Result<Self, FillError> {
//         let base = *instrument.base();
//         let quote = *instrument.quote();

//         if base != quantity.asset() {
//             return Err(FillError::QuantityAssetMismatch {
//                 expected: base,
//                 got: quantity.asset(),
//             });
//         }
//         if quote != price.asset() {
//             return Err(FillError::PriceAssetMismatch {
//                 expected: quote,
//                 got: price.asset(),
//             });
//         }
//         if let Some(fee) = fee {
//             if fee.asset != quote {
//                 return Err(FillError::FeeAssetMismatch {
//                     expected: quote,
//                     got: fee.asset,
//                 });
//             }
//         }

//         Ok(Self {
//             timestamp,
//             instrument,
//             quantity,
//             side,
//             price,
//             fee,
//         })
//     }

//     /// Creates a `Fill` from raw values, validating that the quantity is positive and non-zero.
//     pub fn from_raw(
//         timestamp: DateTime<Utc>,
//         instrument: Arc<Instrument>,
//         quantity: Decimal,
//         side: Side,
//         price: Decimal,
//         fee: Option<Decimal>,
//     ) -> Option<Self> {
//         let base = *instrument.base();
//         let quote = *instrument.quote();
//         let qty = Quantity::new(quantity, base)?;
//         let price = Price::new(price, quote);
//         let fee = fee.map(|f| Amount::new(f, quote));

//         Some(Self {
//             timestamp,
//             instrument,
//             quantity: qty,
//             side,
//             price,
//             fee,
//         })
//     }

//     pub fn timestamp(&self) -> DateTime<Utc> {
//         self.timestamp
//     }

//     pub fn instrument(&self) -> &Instrument {
//         &self.instrument
//     }

//     pub fn quantity(&self) -> Quantity {
//         self.quantity
//     }

//     pub fn side(&self) -> Side {
//         self.side
//     }

//     pub fn price(&self) -> Price {
//         self.price
//     }

//     pub fn fee(&self) -> Option<Amount> {
//         self.fee
//     }
// }
// pub fn add(left: u64, right: u64) -> u64 {
//     left + right
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn it_works() {
//         let result = add(2, 2);
//         assert_eq!(result, 4);
//     }
// }
