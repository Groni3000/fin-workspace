use futchain::{FutChain, ListedTenors};
use instrid::asset::Asset;
use instrid::instruments::TradedInstrument;
use instrid::mic::Mic;
use instrid::prelude::FuturesContract;
use instrid::tenor::Tenor;
use lab::market_data::{Candle, FrdMdReader, MarketData, MdError};
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use std::time::{Duration, Instant};

fn main() -> Result<(), MdError> {
    let dir = Path::new("lab/data/files/futures/frd");
    let instrument: FuturesContract = FuturesContract::new(
        Asset::new("RB", instrid::asset::AssetClass::Commodity).expect("Failed to create Asset"),
        Asset::new("USD", instrid::asset::AssetClass::Currency).expect("Failed to create Asset"),
        Mic::xnym(),
        2025,
        Tenor::December,
        None,
    );
    let listing = ListedTenors::monthly();
    let mut chain = FutChain::new(instrument, &listing).expect("Failed to create FutChain");

    let start = Instant::now();
    let mut total_lines: u64 = 0;
    let mut n_files: u64 = 0;

    // Reused buffer for each record.
    loop {
        let file_path = dir.join(get_frd_file_name(chain.contract()));
        if !file_path.is_file() {
            break;
        }
        println!("Reading file: {:?}", file_path);
        let file = File::open(file_path)?;
        let reader = BufReader::new(file);
        let mut market_data = FrdMdReader::new(reader);
        total_lines += process_contract(&mut market_data)?;
        n_files += 1;

        chain.advance_by(1);
    }

    let duration = start.elapsed();
    println!("---");
    println!(
        "Total number of lines: {}\nTotal number of files: {}
Total duration: {:?}\nAverage amortized time per file: {:?}\n
Average amortized time per line: {:?}",
        total_lines,
        n_files,
        duration,
        Duration::from_nanos(duration.as_nanos() as u64 / n_files as u64),
        Duration::from_nanos(duration.as_nanos() as u64 / total_lines as u64)
    );

    Ok(())
}

fn get_frd_file_name(futures_contract: &FuturesContract) -> String {
    format!(
        "{}_{}{:02}_1min.txt",
        futures_contract.base().name().as_str(),
        futures_contract.tenor().code(),
        futures_contract.year() % 100
    )
}

fn process_contract<T: MarketData>(market_data: &mut T) -> Result<u64, T::Error>
where
    T: MarketData,
    T::Record: Candle,
{
    let file_start = Instant::now();
    let mut lines: u64 = 0;
    let mut last: Option<T::Record> = None;

    while let Some(record) = market_data.next_record()? {
        lines += 1;
        last = Some(record);
    }

    println!(
        "{:>13} lines
        in {:>10?}
        last: {:?}
        ----------",
        lines,
        file_start.elapsed(),
        last,
    );

    Ok(lines)
}
