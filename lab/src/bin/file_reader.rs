use futchain::{FutChain, ListedTenors};
use instrid::asset::Asset;
use instrid::mic::Mic;
use instrid::prelude::FuturesContract;
use instrid::tenor::Tenor;
use lab::market_data::{Candle, FrdFutChainMdReader, FrdMdError, MarketData};
use std::path::Path;
use std::time::{Duration, Instant};

fn main() -> Result<(), FrdMdError> {
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
    let chain = FutChain::new(instrument, &listing).expect("Failed to create FutChain");
    let mut market_data = FrdFutChainMdReader::new(chain, dir.to_path_buf(), String::new())?;

    let start = Instant::now();
    let (total_lines, last_record) = process_contracts(&mut market_data)?;
    let duration = start.elapsed();

    println!(
        "Lines: {:>10}\nDuration: {:>13?}\nDuration per line: {:?}\nLast record:\n{:#?}",
        total_lines,
        duration,
        Duration::from_nanos((duration.as_nanos() / total_lines as u128) as u64),
        last_record,
    );

    Ok(())
}

fn process_contracts<T>(market_data: &mut T) -> Result<(u64, Option<T::Record>), T::Error>
where
    T: MarketData,
    T::Record: Candle,
{
    let mut lines: u64 = 0;
    let mut last: Option<T::Record> = None;

    while let Some(record) = market_data.next_record()? {
        lines += 1;
        last = Some(record);
    }

    Ok((lines, last))
}
