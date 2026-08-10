use std::{
    cmp::Reverse,
    collections::BinaryHeap,
    error::Error,
    fmt::{Debug, Display},
    fs::File,
    io::{BufRead, BufReader},
    path::PathBuf,
};

use chrono::{DateTime, Utc};
use futchain::FutChain;
use instrid::instruments::{FuturesContract, Instrument};
use tradeprim::price::Price;

use crate::formats::{
    Tagged,
    frd::{FrdCandle, FrdCandleParsingError},
};

// ------------------------------
// --- General purpose traits ---
// ------------------------------
pub trait Timestamped {
    fn timestamp(&self) -> DateTime<Utc>;
}

pub trait Instrumented {
    fn instrument(&self) -> Instrument;
}
/// A trait for data that have as little useful data
/// as possible: when and what the price was at that time.
pub trait RelevantPrice: Timestamped {
    fn last_price(&self) -> Price;
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

/// One contract's file, with its next candle read ahead so the merge can compare timestamps.
#[derive(Debug)]
struct Leg {
    contract: FuturesContract,
    reader: BufReader<File>,
    buffer: String,
    pending: Option<FrdCandle>,
}

impl Leg {
    /// `Ok(None)` at end of file. Blank lines are skipped.
    fn read_candle(&mut self) -> Result<Option<FrdCandle>, FrdMdError> {
        loop {
            self.buffer.clear();
            if self.reader.read_line(&mut self.buffer)? == 0 {
                return Ok(None);
            }
            if self.buffer.trim().is_empty() {
                continue;
            }

            return Ok(Some(FrdCandle::from_frd_csv_line(&self.buffer)?));
        }
    }
}

/// Merges every contract file in the chain into one (timestamp, earlies_expiry)-ordered stream.
#[derive(Debug)]
pub struct FrdFutChainMdReader<'a> {
    legs: Vec<Leg>,
    /// Min-heap of `(next timestamp, leg index)`.
    queue: BinaryHeap<Reverse<(DateTime<Utc>, usize)>>,
    /// Leg that produced the last record and still owes a read-ahead.
    refill: Option<usize>,
    chain: FutChain<'a>,
    dir: PathBuf,
}

impl<'a> FrdFutChainMdReader<'a> {
    pub fn new(mut chain: FutChain<'a>, dir: PathBuf) -> Result<Self, FrdMdError> {
        let mut legs = Vec::new();
        loop {
            let path = dir.join(Self::get_file_name(&chain));
            // The first file must exist; the chain ends at the first gap after it.
            if !legs.is_empty() && !path.is_file() {
                break;
            }
            legs.push(Leg {
                contract: *chain.contract(),
                reader: BufReader::new(File::open(&path)?),
                buffer: String::new(),
                pending: None,
            });
            chain.advance();
        }
        chain.retreat_by(legs.len());

        let mut queue = BinaryHeap::with_capacity(legs.len());
        for (idx, leg) in legs.iter_mut().enumerate() {
            if let Some(candle) = leg.read_candle()? {
                queue.push(Reverse((candle.timestamp(), idx)));
                leg.pending = Some(candle);
            }
        }

        Ok(Self {
            legs,
            queue,
            refill: None,
            chain,
            dir,
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

    pub fn chain(&self) -> &FutChain<'a> {
        &self.chain
    }

    pub fn dir(&self) -> &PathBuf {
        &self.dir
    }

    pub fn contracts(&self) -> impl Iterator<Item = &FuturesContract> {
        self.legs.iter().map(|leg| &leg.contract)
    }
}

impl<'a> Iterator for FrdFutChainMdReader<'a> {
    type Item = Result<Tagged<FrdCandle>, FrdMdError>;

    /// Returns None when every file is exhausted.
    fn next(&mut self) -> Option<Self::Item> {
        // Deferred so a read error surfaces without swallowing the record already emitted.
        if let Some(idx) = self.refill.take() {
            match self.legs[idx].read_candle() {
                Ok(Some(candle)) => {
                    self.queue.push(Reverse((candle.timestamp(), idx)));
                    self.legs[idx].pending = Some(candle);
                }
                Ok(None) => {}
                Err(e) => return Some(Err(e)),
            }
        }

        let Reverse((_, idx)) = self.queue.pop()?;
        let leg = &mut self.legs[idx];
        let candle = leg
            .pending
            .take()
            .expect("a queued leg always holds a candle");
        let instrument = Instrument::Futures(leg.contract);
        self.refill = Some(idx);

        Some(Ok(Tagged::new(instrument, candle)))
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
