use crate::rust_backend::SMA;
use pyo3::prelude::*;

/// Parameters for configuring a Average Range (AR) indicator.
///
/// # Fields
/// * `period` - The window size for the RSI calculation. Must be at least 1.
#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    #[pyo3(get)]
    sma_parameters: SMA::Parameters,
}

#[pymethods]
impl Parameters {
    /// Creates a new Parameters instance with the specified period.
    ///
    /// # Arguments
    /// * `period` - The window size for the AR. Must be at least 1.
    ///
    /// # Errors
    /// Returns a PyValueError if period is 0.
    #[new]
    fn new(sma_parameters: SMA::Parameters) -> Self {
        Parameters { sma_parameters }
    }
}

#[pyclass]
pub struct Indicator {
    rolling_mean_height: SMA::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> Self {
        Indicator {
            rolling_mean_height: SMA::Indicator::new(&parameters.sma_parameters),
        }
    }

    pub fn update(&mut self, high_price: f64, low_price: f64) -> f64 {
        let height = high_price - low_price;
        self.rolling_mean_height.update(height)
    }
}
