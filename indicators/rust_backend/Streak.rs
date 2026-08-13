use std::{cmp::Ordering, f64};

use pyo3::{pyclass, pymethods};

#[pyclass]
#[derive(Clone)]
pub struct Parameters {}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new() -> Self {
        Self {}
    }
}

#[pyclass]
pub struct Indicator {
    streak: i64,
    previous_price: f64,
}

#[pymethods]
impl Indicator {
    #[new]
    #[allow(unused_variables)]
    pub fn new(parameters: Parameters) -> Self {
        Self {
            streak: 0,
            previous_price: f64::NAN,
        }
    }

    pub fn update(&mut self, price: f64) -> i64 {
        let difference = price - self.previous_price;
        match difference.partial_cmp(&0.0) {
            Some(Ordering::Equal) | None => self.streak = 0,
            Some(Ordering::Greater) => self.streak = (self.streak + 1).max(1),
            Some(Ordering::Less) => self.streak = (self.streak - 1).min(-1),
        }

        self.previous_price = price;

        self.streak
    }
}
