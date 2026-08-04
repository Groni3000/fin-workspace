use std::{
    error::Error,
    fmt::{Debug, Display},
    fs::File,
    io::{BufRead, BufReader},
    path::PathBuf,
};

use chrono::{DateTime, Utc};
use futchain::FutChain;
use tradeprim::price::Price;

use crate::{FrdCandle, FrdCandleParsingError};

// ------------------------------
// --- General purpose traits ---
// ------------------------------
pub trait Timestamped {
    fn timestamp(&self) -> DateTime<Utc>;
}
/// A trait for data that have as little useful data
/// as possible: when and what the price was at that time.
pub trait RelevantPrice: Timestamped {
    fn last_price(&self) -> Price;
}

/// Represents an unknown time span aggregated candle.
///
/// Naturally extends RelevantPrice.
pub trait Candle: RelevantPrice + Debug {
    fn open(&self) -> Price;
    fn high(&self) -> Price;
    fn low(&self) -> Price;
    fn close(&self) -> Price;
    fn volume(&self) -> u64;
}

pub trait MarketData: Iterator<Item = Result<Self::Record, Self::Error>> {
    type Record: Debug + RelevantPrice + Ord + Eq;
    type Error;
}

impl<T, R, E> MarketData for T
where
    T: Iterator<Item = Result<R, E>>,
    R: Debug + RelevantPrice + Ord + Eq,
    E: Error,
{
    type Record = R;
    type Error = E;
}

// --------------
// --- Errors ---
// --------------
#[derive(Debug)]
pub enum FrdMdError {
    Io(std::io::Error),
    Parse(FrdCandleParsingError),
}

impl Display for FrdMdError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FrdMdError::Io(e) => write!(f, "IO error: {}", e),
            FrdMdError::Parse(e) => write!(f, "Parse error: {}", e),
        }
    }
}

impl std::error::Error for FrdMdError {}

impl From<std::io::Error> for FrdMdError {
    fn from(e: std::io::Error) -> Self {
        FrdMdError::Io(e)
    }
}

impl From<FrdCandleParsingError> for FrdMdError {
    fn from(e: FrdCandleParsingError) -> Self {
        FrdMdError::Parse(e)
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
    pub fn new(chain: FutChain<'a>, dir: PathBuf, buffer: String) -> Result<Self, FrdMdError> {
        let file_name = Self::get_file_name(&chain);
        let file = File::open(dir.join(&file_name))?;
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

    fn advance(&mut self) -> Result<bool, FrdMdError> {
        self.chain.advance();
        let file_name = Self::get_file_name(&self.chain);
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

impl<'a> Iterator for FrdFutChainMdReader<'a> {
    type Item = Result<FrdCandle, FrdMdError>;

    /// Returns None when files exhausted.
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            self.buffer.clear();
            let n = match self.current.read_line(&mut self.buffer) {
                Ok(n) => n,
                Err(e) => return Some(Err(e.into())),
            };
            if n == 0 {
                match self.advance() {
                    // File found
                    Ok(true) => continue,
                    // File not found
                    Ok(false) => return None,
                    // Error reading file
                    Err(e) => return Some(Err(e)),
                }
            }
            let record = match FrdCandle::from_frd_csv_line(&self.buffer) {
                Ok(record) => record,
                Err(e) => return Some(Err(e.into())),
            };

            return Some(Ok(record));
        }
    }
}

// impl<'a> MarketData for FrdFutChainMdReader<'a> {
//     type Record = FrdCandle;
//     type Error = FrdMdError;

//     fn next_record(&mut self) -> Result<Option<Self::Record>, Self::Error> {
//         loop {
//             self.buffer.clear();
//             let n = self.current.read_line(&mut self.buffer)?;
//             if n == 0 {
//                 if self.advance()? {
//                     continue;
//                 }
//                 // No next file, signal end of stream
//                 return Ok(None);
//             }
//             let record = FrdCandle::from_frd_csv_line(&self.buffer)?;

//             return Ok(Some(record));
//         }
//     }
// }

// /// A reader that reads market data into a buffer.
// #[derive(Debug)]
// pub struct FrdMdReader<T: BufRead> {
//     reader: T,
//     buffer: String,
// }

// impl<T: BufRead> FrdMdReader<T> {
//     pub fn new(reader: T) -> Self {
//         Self {
//             reader,
//             buffer: String::new(),
//         }
//     }

//     pub fn with_capacity(reader: T, n: usize) -> Self {
//         Self {
//             reader,
//             buffer: String::with_capacity(n),
//         }
//     }
// }

// impl<T: BufRead> MarketData for FrdMdReader<T> {
//     type Record = FrdCandle;
//     type Error = FrdMdError;

//     fn next_record(&mut self) -> Result<Option<Self::Record>, Self::Error> {
//         self.buffer.clear();
//         let n = self.reader.read_line(&mut self.buffer)?;

//         if n == 0 {
//             return Ok(None);
//         }
//         let record = FrdCandle::from_frd_csv_line(&self.buffer)?;

//         Ok(Some(record))
//     }
// }
