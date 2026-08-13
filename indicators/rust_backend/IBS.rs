use pyo3::prelude::*;

#[pyclass]
pub struct Parameters {}

#[pyclass]
pub struct Indicator {}

#[pymethods]
impl Parameters {
    #[new]
    fn new() -> Self {
        Parameters {}
    }
}

#[pymethods]
impl Indicator {
    #[allow(unused_variables)]
    #[new]
    fn new(parameters: &Parameters) -> Self {
        Indicator {}
    }

    /// (Close - Low) / (High - Low)
    pub fn update(&self, high_price: f64, low_price: f64, close_price: f64) -> f64 {
        (close_price - low_price) / (high_price - low_price)
    }
}
