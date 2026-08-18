use oms::order::{New, Order};
use tradeprim::position::Position;

#[derive(Debug, Default)]
pub struct Desired {
    desired_position: Position,
    desired_orders: Vec<Order<New>>,
}

impl Desired {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn dp(&self) -> &Position {
        &self.desired_position
    }

    pub fn des_ords(&self) -> &Vec<Order<New>> {
        &self.desired_orders
    }

    pub fn dp_mut(&mut self) -> &mut Position {
        &mut self.desired_position
    }

    pub fn desired_orders_mut(&mut self) -> &mut Vec<Order<New>> {
        &mut self.desired_orders
    }

    /// Sets (overwrites) the desired position to the given position.
    pub fn set_desired_position(&mut self, desired_position: Position) {
        self.desired_position = desired_position;
    }
}
