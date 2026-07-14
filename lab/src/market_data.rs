use std::{fmt::Debug, io::BufRead};

use chrono::{DateTime, Utc};
use tradeprim::price::Price;

use crate::{FrdCandle, FrdCandleParsingError};

// ------------------------------
// --- General purpose traits ---
// ------------------------------
pub trait RelevantPrice {
    fn last_price(&self) -> Price;
    fn timestamp(&self) -> DateTime<Utc>;
}

pub trait Candle: RelevantPrice {
    fn open(&self) -> Price;
    fn high(&self) -> Price;
    fn low(&self) -> Price;
    fn close(&self) -> Price;
    fn volume(&self) -> u64;
}

pub trait MarketData {
    type Record: Debug;
    type Error;

    /// Returns the next record, if one is available.
    fn next_record(&mut self) -> Result<Option<Self::Record>, Self::Error>;
}
// --------------
// --- Errors ---
// --------------
#[derive(Debug)]
pub enum MdError {
    Io(std::io::Error),
    Parse(FrdCandleParsingError),
}

impl From<std::io::Error> for MdError {
    fn from(e: std::io::Error) -> Self {
        MdError::Io(e)
    }
}

impl From<FrdCandleParsingError> for MdError {
    fn from(e: FrdCandleParsingError) -> Self {
        MdError::Parse(e)
    }
}

// ---------------
// --- Structs ---
// ---------------

/// A reader that reads market data into a buffer.
#[derive(Debug)]
pub struct FrdMdReader<T: BufRead> {
    reader: T,
    buffer: String,
}

impl<T: BufRead> FrdMdReader<T> {
    pub fn new(reader: T) -> Self {
        Self {
            reader,
            buffer: String::new(),
        }
    }

    pub fn with_capacity(reader: T, n: usize) -> Self {
        Self {
            reader,
            buffer: String::with_capacity(n),
        }
    }
}

impl<T: BufRead> MarketData for FrdMdReader<T> {
    type Record = FrdCandle;
    type Error = MdError;

    fn next_record(&mut self) -> Result<Option<Self::Record>, Self::Error> {
        self.buffer.clear();
        let n = self.reader.read_line(&mut self.buffer)?;

        if n == 0 {
            return Ok(None);
        }
        let record = FrdCandle::from_frd_csv_line(&self.buffer)?;

        Ok(Some(record))
    }
}
