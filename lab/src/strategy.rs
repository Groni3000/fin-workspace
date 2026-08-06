use std::collections::HashMap;

use oms::{
    OrderId,
    order::{New, Order},
};
use tradeprim::position::Position;

#[derive(Default)]
pub struct Desired {
    position: Position,
    orders: HashMap<OrderId, Order<New>>,
    // cancels: Vec<OrderId>,
}

impl Desired {
    pub fn new(position: Position, orders: HashMap<OrderId, Order<New>>) -> Self {
        Self { position, orders }
    }

    pub fn position(&self) -> Position {
        self.position
    }

    pub fn orders(&self) -> &HashMap<OrderId, Order<New>> {
        &self.orders
    }

    pub fn mut_position(&mut self) -> &mut Position {
        &mut self.position
    }
}
