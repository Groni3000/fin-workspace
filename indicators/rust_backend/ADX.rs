use crate::rust_backend::{DI, SMA};
use pyo3::{pyclass, pymethods};

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    di_parameters: DI::Parameters,
    sma_parameters: SMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(di_parameters: DI::Parameters, sma_parameters: SMA::Parameters) -> Self {
        Parameters {
            di_parameters,
            sma_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    di_indicator: DI::Indicator,
    sma_indicator: SMA::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: Parameters) -> Self {
        let di_indicator = DI::Indicator::new(&parameters.di_parameters);
        let sma_indicator = SMA::Indicator::new(&parameters.sma_parameters);

        Indicator {
            di_indicator,
            sma_indicator,
        }
    }

    pub fn update(&mut self, high_price: f64, low_price: f64, close_price: f64) -> f64 {
        let (positive_directional_index, negative_directional_index) =
            self.di_indicator.update(high_price, low_price, close_price);

        100.0
            * self.sma_indicator.update(
                (positive_directional_index - negative_directional_index).abs()
                    / (positive_directional_index + negative_directional_index),
            )
    }
}
