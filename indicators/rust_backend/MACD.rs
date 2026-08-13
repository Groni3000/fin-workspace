use pyo3::{pyclass, pymethods};

use crate::rust_backend::EWMA;

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    fast_ewma_parameters: EWMA::Parameters,
    slow_ewma_parameters: EWMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(
        fast_ewma_parameters: EWMA::Parameters,
        slow_ewma_parameters: EWMA::Parameters,
    ) -> Self {
        Self {
            fast_ewma_parameters,
            slow_ewma_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    fast_ewma: EWMA::Indicator,
    slow_ewma: EWMA::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> Self {
        let fast = EWMA::Indicator::new(&parameters.fast_ewma_parameters);
        let slow = EWMA::Indicator::new(&parameters.slow_ewma_parameters);

        Self {
            fast_ewma: fast,
            slow_ewma: slow,
        }
    }

    pub fn update(&mut self, price: f64) -> f64 {
        let fast_value = self.fast_ewma.update(price);
        let slow_value = self.slow_ewma.update(price);

        fast_value - slow_value
    }
}
