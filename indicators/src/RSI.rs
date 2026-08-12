use crate::SMA;
use std::cmp::Ordering;

/// Parameters for configuring a Relative Strength Index (RSI) indicator.
///
/// # Fields
/// * `period` - The window size for the RSI calculation. Must be at least 1.
#[derive(Debug, Clone, Copy)]
pub struct Parameters {
    sma_parameters: SMA::Parameters,
}

impl Parameters {
    /// Creates a new Parameters instance with the specified period.
    ///
    /// # Arguments
    /// * `period` - The window size for the RSI. Must be at least 1.
    ///
    /// # Errors
    /// Returns a PyValueError if period is 0.
    pub fn new(sma_parameters: SMA::Parameters) -> Self {
        Parameters { sma_parameters }
    }
}

pub struct Indicator {
    parameters: Parameters,
    last_price: Option<f64>,
    rolling_gain: SMA::Indicator,
    rolling_loss: SMA::Indicator,
}

impl Indicator {
    pub fn new(parameters: Parameters) -> Self {
        Indicator {
            parameters,
            last_price: None,
            rolling_gain: SMA::Indicator::new(parameters.sma_parameters),
            rolling_loss: SMA::Indicator::new(parameters.sma_parameters),
        }
    }

    pub fn update(&mut self, price: f64) -> f64 {
        if price.is_nan() || price.is_infinite() {
            self.last_price = None;
            self.rolling_gain.clear();
            self.rolling_loss.clear();

            return f64::NAN;
        }
        let price_difference = match self.last_price {
            Some(last_price) => price - last_price,
            None => {
                self.last_price = Some(price);
                return f64::NAN;
            }
        };

        self.last_price = Some(price);

        let (current_gain, current_loss) = match price_difference.total_cmp(&0.0) {
            Ordering::Greater => (
                self.rolling_gain.update(price_difference),
                self.rolling_loss.update(0.0),
            ),
            Ordering::Less => (
                self.rolling_gain.update(0.0),
                self.rolling_loss.update(-price_difference),
            ),
            Ordering::Equal => (self.rolling_gain.update(0.0), self.rolling_loss.update(0.0)),
        };

        // Check for early exits
        if current_loss.is_nan() {
            return f64::NAN;
        }
        if current_loss == 0.0 {
            if current_gain == 0.0 {
                return f64::NAN;
            } else {
                return 100.0;
            }
        };
        // Check ended
        let rs = current_gain / current_loss;
        let rsi = 100.0 - (100.0 / (1.0 + rs));

        rsi
    }

    pub fn parameters(&self) -> Parameters {
        self.parameters
    }
}
