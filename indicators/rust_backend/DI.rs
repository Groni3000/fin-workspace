use crate::rust_backend::{ATR, SMA};
use pyo3::{pyclass, pymethods};

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    atr_parameters: ATR::Parameters,
    sma_parameters: SMA::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(atr_parameters: ATR::Parameters, sma_parameters: SMA::Parameters) -> Self {
        Parameters {
            atr_parameters,
            sma_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    atr_indicator: ATR::Indicator,
    positive_sma_indicator: SMA::Indicator,
    negative_sma_indicator: SMA::Indicator,
    previous_high_price: f64,
    previous_low_price: f64,
}
#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> Self {
        let atr_indicator = ATR::Indicator::new(&parameters.atr_parameters);
        let positive_sma_indicator = SMA::Indicator::new(&parameters.sma_parameters);
        let negative_sma_indicator = SMA::Indicator::new(&parameters.sma_parameters);

        Self {
            atr_indicator,
            positive_sma_indicator,
            negative_sma_indicator,
            previous_high_price: f64::NAN,
            previous_low_price: f64::NAN,
        }
    }

    /// Returns:
    ///     - (positive directional index, negative directional index)
    pub fn update(&mut self, high_price: f64, low_price: f64, close_price: f64) -> (f64, f64) {
        let atr_value = self
            .atr_indicator
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
        let positive_sma = self.positive_sma_indicator.update(directional_movements.0);
        let negative_sma = self.negative_sma_indicator.update(directional_movements.1);

        (
            100.0 * positive_sma / atr_value,
            100.0 * negative_sma / atr_value,
        )
    }
}

/// (Positive dm, negative dm)
struct DirectionalMovements(f64, f64);
