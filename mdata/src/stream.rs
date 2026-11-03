//! A source of market-data records.

use std::{error::Error, fmt::Debug};

use crate::record::RelevantPrice;

/// A fallible stream of market-data records.
///
/// Blanket-implemented for every `Iterator<Item = Result<R, E>>` whose record
/// has at least a [`RelevantPrice`] and whose error is an [`Error`].
pub trait MarketData: Iterator<Item = Result<Self::Record, Self::Error>> {
    type Record: Debug + RelevantPrice;
    type Error;
}

impl<T, R, E> MarketData for T
where
    T: Iterator<Item = Result<R, E>>,
    R: Debug + RelevantPrice,
    E: Error,
{
    type Record = R;
    type Error = E;
}
