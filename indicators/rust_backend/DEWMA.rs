use pyo3::{PyResult, pyclass, pymethods};
use crate::rust_backend::EWMA;

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    #[pyo3(get)]
    pub ewma_parameters: EWMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(ewma_parameters: EWMA::Parameters) -> Self {
        Self { ewma_parameters }
    }
}

#[pyclass]
pub struct Indicator {
    #[pyo3(get)]
    pub parameters: Parameters,
    ewma: EWMA::Indicator,
    ewma_ewma: EWMA::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: Parameters) -> PyResult<Self> {
        let ewma = EWMA::Indicator::new(&parameters.ewma_parameters);
        let ewma_ewma = EWMA::Indicator::new(&parameters.ewma_parameters);

        Ok(Self { parameters, ewma, ewma_ewma })
    }

    pub fn update(&mut self, price: f64) -> f64 {
        let e = self.ewma.update(price);
        let ee = self.ewma_ewma.update(e);

        2.0 * e - ee
    }
}
