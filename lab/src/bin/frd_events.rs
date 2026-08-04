use std::{iter::Peekable, path::Path};

use futchain::{FutChain, ListedTenors};
use instrid::{asset::Asset, instruments::FuturesContract, mic::MicIso, tenor::Tenor};
use lab::{
    event::EventSource,
    events_impls::frd::FrdEventQueue,
    market_data::{FrdFutChainMdReader, FrdMdError},
};
use tradeprim::currency::Currency;

fn main() -> Result<(), FrdMdError> {
    let dir = Path::new("lab/data/files/futures/frd");
    let instrument: FuturesContract = FuturesContract::new_unchecked(
        Asset::new("RB", instrid::asset::AssetClass::Commodity).expect("Failed to create Asset"),
        Asset::new("USD", instrid::asset::AssetClass::Currency).expect("Failed to create Asset"),
        MicIso::xnym().into(),
        Currency::usd(),
        2025,
        Tenor::December,
        None,
    );
    let listing = ListedTenors::monthly();
    let chain = FutChain::new(instrument, &listing).expect("Failed to create FutChain");
    let market_data = FrdFutChainMdReader::new(chain, dir.to_path_buf(), String::new())?.peekable();

    let mut event_queue = FrdEventQueue::new(0, 0, market_data);

    while let Some(event) = event_queue.next_event() {
        println!("{:?}", event);
    }

    Ok(())
}
