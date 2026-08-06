use std::collections::HashMap;

use instrid::instruments::Instrument;
use oms::{
    fill::Fill,
    order::{Order, Terminated},
};
use tradeprim::position::Position;

pub struct Portfolio {
    positions: HashMap<Instrument, Position>,
    fills: Vec<Fill>,
    orders: Vec<Order<Terminated>>,
}

impl Portfolio {
    pub fn position(&self, instrument: &Instrument) -> &Position {
        self.positions.get(instrument).unwrap_or(&Position::Flat)
    }

    pub fn push_fill(&mut self, fill: Fill) {
        *(self.positions.entry(fill.instrument()).or_default()) += fill.as_position();
        self.fills.push(fill);
    }

    pub fn push_order(&mut self, order: Order<Terminated>) {
        self.orders.push(order);
    }
}

impl Portfolio {
    pub fn new() -> Self {
        Self {
            positions: HashMap::new(),
            fills: Vec::new(),
            orders: Vec::new(),
        }
    }

    pub fn positions(&self) -> &HashMap<Instrument, Position> {
        &self.positions
    }

    pub fn fills(&self) -> &[Fill] {
        &self.fills
    }
}
