use crate::rust_backend::{EWMA, TR};
use pyo3::prelude::*;

#[pyclass]
// Clone is needed to include this struct
// into enum for different indicators
#[derive(Clone)]
pub struct Parameters {
    #[pyo3(get)]
    tr_parameters: TR::Parameters,
    #[pyo3(get)]
    ewma_parameters: EWMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    fn new(tr_parameters: TR::Parameters, ewma_parameters: EWMA::Parameters) -> PyResult<Self> {
        Ok(Parameters {
            tr_parameters,
            ewma_parameters,
        })
    }
}

impl Parameters {
    pub fn get_tr_parameters(&self) -> &TR::Parameters {
        &self.tr_parameters
    }
    pub fn get_ewma_parameters(&self) -> &EWMA::Parameters {
        &self.ewma_parameters
    }
}

#[pyclass]
pub struct Indicator {
    tr_indicator: TR::Indicator,
    ewma_indicator: EWMA::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> PyResult<Self> {
        let tr_parameters = parameters.get_tr_parameters();
        let ewma_parameters = parameters.get_ewma_parameters();

        Ok(Indicator {
            tr_indicator: TR::Indicator::new(tr_parameters),
            ewma_indicator: EWMA::Indicator::new(ewma_parameters),
        })
    }

    pub fn update(&mut self, high_price: f64, low_price: f64, current_close_price: f64) -> f64 {
        let tr_value = self
            .tr_indicator
            .update(high_price, low_price, current_close_price);

        let ewma_value = self.ewma_indicator.update(tr_value);

        ewma_value
    }
}
