use crate::rust_backend::{SMA, TR};
use pyo3::prelude::*;

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    #[pyo3(get)]
    tr_parameters: TR::Parameters,
    #[pyo3(get)]
    sma_parameters: SMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    fn new(tr_parameters: TR::Parameters, sma_parameters: SMA::Parameters) -> Self {
        Parameters {
            tr_parameters,
            sma_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    tr_indicator: TR::Indicator,
    rolling_sma: SMA::Indicator,
    #[pyo3(get)]
    parameters: Parameters,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> Self {
        Indicator {
            tr_indicator: TR::Indicator::new(&parameters.tr_parameters),
            rolling_sma: SMA::Indicator::new(&parameters.sma_parameters),
            parameters: parameters.clone(),
        }
    }

    pub fn update(&mut self, high_price: f64, low_price: f64, close_price: f64) -> f64 {
        let tr_value = self.tr_indicator.update(high_price, low_price, close_price);

        let sma_value = self.rolling_sma.update(tr_value);

        sma_value
    }
}
