use oms::{
    OrderId,
    order::{New, Order},
};
use tradeprim::position::Position;

#[derive(Debug, Default)]
pub struct Desired {
    desired_position: Position,
    desired_orders: Vec<Order<New>>,
    desired_protected_position: Position,
    desired_protective_orders: Vec<Order<New>>,
    desired_cancels: Vec<OrderId>,
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

    pub fn dpp(&self) -> &Position {
        &self.desired_protected_position
    }

    pub fn des_prot_ords(&self) -> &Vec<Order<New>> {
        &self.desired_protective_orders
    }

    pub fn dp_mut(&mut self) -> &mut Position {
        &mut self.desired_position
    }

    pub fn desired_orders_mut(&mut self) -> &mut Vec<Order<New>> {
        &mut self.desired_orders
    }

    pub fn desired_cancels(&self) -> &[OrderId] {
        &self.desired_cancels
    }

    pub fn desired_cancels_mut(&mut self) -> &mut Vec<OrderId> {
        &mut self.desired_cancels
    }

    pub fn desired_protective_orders_mut(&mut self) -> &mut Vec<Order<New>> {
        &mut self.desired_protective_orders
    }
}
