use pyo3::{PyResult, pyclass, pymethods};
use crate::rust_backend::{WilderDI, EWMA};

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    wilder_di_parameters: WilderDI::Parameters,
    ewma_parameters: crate::rust_backend::EWMA::Parameters
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(wilder_di_parameters: WilderDI::Parameters, ewma_parameters: crate::rust_backend::EWMA::Parameters) -> Self {
        Self {
            wilder_di_parameters,
            ewma_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    wilder_di_indicator: WilderDI::Indicator,
    ewma_indicator: EWMA::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> PyResult<Self> {
        let wilder_di_indicator = WilderDI::Indicator::new(&parameters.wilder_di_parameters)?;
        let ewma_indicator = EWMA::Indicator::new(&parameters.ewma_parameters);

        Ok(Self {
            wilder_di_indicator,
            ewma_indicator,
        })
    }

    pub fn update(&mut self, high_price: f64, low_price: f64, close_price: f64) -> f64 {
        let (positive_directional_index, negative_directional_index) =
            self.wilder_di_indicator.update(high_price, low_price, close_price);

        100.0
            * self.ewma_indicator.update(
                (positive_directional_index - negative_directional_index).abs()
                    / (positive_directional_index + negative_directional_index),
            )
    }
}