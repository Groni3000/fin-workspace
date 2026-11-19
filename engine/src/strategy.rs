//! What the event loop needs of a strategy.

use foldhash::HashMap;
use instrid::instruments::Instrument;
use oms::{desired::Desired, portfolio::Portfolio};

use crate::event::Event;

/// A strategy the main loop can drive on:
///   - reacts to every event
///   - says what it wants to hold.
///
/// Named `Traded` rather than `Strategy` because strategy structs are usually called `Strategy`.
pub trait Traded<R> {
    fn on_event(&mut self, event: &Event<R>, pf: &Portfolio);

    /// The position and orders wanted per instrument. Only the strategy writes it.
    fn desired(&self) -> &HashMap<Instrument, Desired>;
}
