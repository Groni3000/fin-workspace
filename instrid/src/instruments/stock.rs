use crate::asset::Asset;
use crate::instrument::BaseInstrument;
use crate::mic::Mic;

#[derive(Debug, PartialEq, Eq)]
pub struct Stock {
    base: Asset,
    quote: Asset,
    mic: Mic,
}

impl BaseInstrument for Stock {
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
