use pyo3::{pyclass, pymethods};

use crate::rust_backend::{EWMA, MACD};

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    macd_parameters: MACD::Parameters,
    ewma_parameters: EWMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(macd_parameters: MACD::Parameters, ewma_parameters: EWMA::Parameters) -> Self {
        Self {
            macd_parameters,
            ewma_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    macd_indicator: MACD::Indicator,
    ewma_indicator: EWMA::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> Self {
        let macd_indicator = MACD::Indicator::new(&parameters.macd_parameters);
        let ewma_indicator = EWMA::Indicator::new(&parameters.ewma_parameters);

        Self {
            macd_indicator,
            ewma_indicator,
        }
    }

    pub fn update(&mut self, price: f64) -> f64 {
        let macd = self.macd_indicator.update(price);
        let signal_line = self.ewma_indicator.update(macd);

        return signal_line;
    }
}
