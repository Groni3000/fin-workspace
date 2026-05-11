use crate::asset::Asset;
use crate::instrument::BaseInstrument;
use crate::mic::Mic;
use crate::tenor::Tenor;

#[derive(Debug, PartialEq, Eq)]
pub struct Futures {
    base: Asset,
    quote: Asset,
    mic: Mic,
    year: u16,
    tenor: Tenor,
    day: Option<u8>,
}

impl Futures {
    pub const fn new(
        base: Asset,
        quote: Asset,
        mic: Mic,
        year: u16,
        tenor: Tenor,
        day: Option<u8>,
    ) -> Self {
        Self {
            base,
            quote,
            mic,
            year,
            tenor,
            day,
        }
    }
}

impl BaseInstrument for Futures {
    fn base(&self) -> &Asset {
        &self.base
    }

    fn quote(&self) -> &Asset {
        &self.quote
    }

    fn mic(&self) -> &Mic {
        &self.mic
    }
}
