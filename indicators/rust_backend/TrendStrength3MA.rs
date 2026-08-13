use pyo3::{PyResult, pyclass, pymethods};
use crate::rust_backend::SMA;

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    #[pyo3(get)]
    pub sma1_parameters: SMA::Parameters,
    #[pyo3(get)]
    pub sma2_parameters: SMA::Parameters,
    #[pyo3(get)]
    pub sma3_parameters: SMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(
        sma1_parameters: SMA::Parameters,
        sma2_parameters: SMA::Parameters,
        sma3_parameters: SMA::Parameters,
    ) -> Self {
        Self {
            sma1_parameters,
            sma2_parameters,
            sma3_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    #[pyo3(get)]
    pub parameters: Parameters,
    sma1: SMA::Indicator,
    sma2: SMA::Indicator,
    sma3: SMA::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> PyResult<Self> {
        let sma1 = SMA::Indicator::new(&parameters.sma1_parameters);
        let sma2 = SMA::Indicator::new(&parameters.sma2_parameters);
        let sma3 = SMA::Indicator::new(&parameters.sma3_parameters);

        Ok(Self { parameters: parameters.clone(), sma1, sma2, sma3 })
    }

    pub fn update(&mut self, price: f64) -> f64 {
        let sma1_value = self.sma1.update(price);
        let sma2_value = self.sma2.update(price);
        let sma3_value = self.sma3.update(price);

        let a1 = (price > sma1_value) as i32 as f64;
        let a2 = (price > sma2_value) as i32 as f64;
        let a3 = (price > sma3_value) as i32 as f64;

        a1 + a2 + a3
    }
}
