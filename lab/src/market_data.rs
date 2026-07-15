use std::{
    fmt::Debug,
    fs::File,
    io::{BufRead, BufReader},
    path::PathBuf,
};

use chrono::{DateTime, Utc};
use futchain::FutChain;
use instrid::instruments::TradedInstrument;
use tradeprim::price::Price;

use crate::{FrdCandle, FrdCandleParsingError};

// ------------------------------
// --- General purpose traits ---
// ------------------------------
/// A trait for data that have as little useful data
/// as possible: when and what the price was at that time.
pub trait RelevantPrice {
    fn last_price(&self) -> Price;
    fn timestamp(&self) -> DateTime<Utc>;
}

/// Represents an unknown time span aggregated candle.
///
/// Naturally extends RelevantPrice.
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
pub struct FrdFutChainMdReader<'a> {
    current: BufReader<File>,
    chain: FutChain<'a>,
    dir: PathBuf,
    buffer: String,
}

impl<'a> FrdFutChainMdReader<'a> {
    pub fn new(chain: FutChain<'a>, dir: PathBuf, buffer: String) -> Result<Self, MdError> {
        let file_name = Self::get_file_name(&chain);
        let file = File::open(&dir.join(&file_name))?;
        let reader = BufReader::new(file);

        Ok(Self {
            current: reader,
            chain,
            dir,
            buffer,
        })
    }

    fn get_file_name(chain: &FutChain) -> String {
        let contract = chain.contract();
        format!(
            "{}_{}{:02}_1min.txt",
            contract.base().name().as_str(),
            contract.tenor().code(),
            contract.year() % 100
        )
    }

    fn advance(&mut self) -> Result<bool, MdError> {
        self.chain.advance();
        let file_name = Self::get_file_name(self.chain());
        let path = self.dir.join(&file_name);
        if !path.is_file() {
            return Ok(false);
        }
        self.current = BufReader::new(File::open(&path)?);

        Ok(true)
    }

    pub fn chain(&self) -> &FutChain<'a> {
        &self.chain
    }

    pub fn dir(&self) -> &PathBuf {
        &self.dir
    }
}

impl<'a> MarketData for FrdFutChainMdReader<'a> {
    type Record = FrdCandle;
    type Error = MdError;

    fn next_record(&mut self) -> Result<Option<Self::Record>, Self::Error> {
        loop {
            self.buffer.clear();
            let n = self.current.read_line(&mut self.buffer)?;
            if n == 0 {
                if self.advance()? {
                    continue;
                }
                // No next file, signal end of stream
                return Ok(None);
            }
            let record = FrdCandle::from_frd_csv_line(&self.buffer)?;

            return Ok(Some(record));
        }
    }
}

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
