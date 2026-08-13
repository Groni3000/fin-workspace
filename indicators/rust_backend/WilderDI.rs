use std::f64;

use pyo3::{pyclass, pymethods, PyResult};

use crate::rust_backend::{WilderATR, EWMA};

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    wilder_atr_parameters: WilderATR::Parameters,
    ewma_parameters: EWMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(
        wilder_atr_parameters: WilderATR::Parameters,
        ewma_parameters: EWMA::Parameters,
    ) -> Self {
        Self {
            wilder_atr_parameters,
            ewma_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    wilder_atr_indicator: WilderATR::Indicator,
    positive_ewma_indicator: EWMA::Indicator,
    negative_ewma_indicator: EWMA::Indicator,
    previous_high_price: f64,
    previous_low_price: f64,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> PyResult<Self> {
        let wilder_atr_indicator = WilderATR::Indicator::new(&parameters.wilder_atr_parameters)?;
        let positive_ewma_indicator = EWMA::Indicator::new(&parameters.ewma_parameters);
        let negative_ewma_indicator = EWMA::Indicator::new(&parameters.ewma_parameters);

        Ok(Self {
            wilder_atr_indicator,
            positive_ewma_indicator,
            negative_ewma_indicator,
            previous_high_price: f64::NAN,
            previous_low_price: f64::NAN,
        })
    }

    /// Returns:
    ///     - (positive directional index, negative directional index)
    pub fn update(&mut self, high_price: f64, low_price: f64, close_price: f64) -> (f64, f64) {
        let atr_value = self
            .wilder_atr_indicator
            .update(high_price, low_price, close_price);
        let directional_movements = self.calculate_directional_movements(high_price, low_price);

        self.calculate_directional_indices(directional_movements, atr_value)
    }
}

impl Indicator {
    fn calculate_directional_movements(
        &mut self,
        high_price: f64,
        low_price: f64,
    ) -> DirectionalMovements {
        let up_move = high_price - self.previous_high_price;
        let down_move = self.previous_low_price - low_price;

        let positive = match (up_move > 0.0, up_move > down_move) {
            (true, true) => up_move,
            (_, _) => 0.0,
        };
        let negative = match (down_move > 0.0, down_move > up_move) {
            (true, true) => down_move,
            (_, _) => 0.0,
        };

        self.previous_low_price = low_price;
        self.previous_high_price = high_price;

        DirectionalMovements(positive, negative)
    }

    fn calculate_directional_indices(
        &mut self,
        directional_movements: DirectionalMovements,
        atr_value: f64,
    ) -> (f64, f64) {
        let positive_sma = self.positive_ewma_indicator.update(directional_movements.0);
        let negative_sma = self.negative_ewma_indicator.update(directional_movements.1);

        (
            100.0 * positive_sma / atr_value,
            100.0 * negative_sma / atr_value,
        )
    }
}

/// (Positive dm, negative dm)
struct DirectionalMovements(f64, f64);
