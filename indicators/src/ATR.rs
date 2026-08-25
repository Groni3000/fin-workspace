use crate::{SMA, TR};

#[derive(Debug, Clone, Copy)]
pub struct Parameters {
    tr_parameters: TR::Parameters,
    sma_parameters: SMA::Parameters,
}

impl Parameters {
    pub fn new(tr_parameters: TR::Parameters, sma_parameters: SMA::Parameters) -> Self {
        Parameters {
            tr_parameters,
            sma_parameters,
        }
    }

    pub fn tr_parameters(&self) -> TR::Parameters {
        self.tr_parameters
    }

    pub fn sma_parameters(&self) -> SMA::Parameters {
        self.sma_parameters
    }
}

#[derive(Debug)]
pub struct Indicator {
    tr_indicator: TR::Indicator,
    rolling_sma: SMA::Indicator,
    parameters: Parameters,
}

impl Indicator {
    pub fn new(parameters: Parameters) -> Self {
        Indicator {
            tr_indicator: TR::Indicator::new(parameters.tr_parameters),
            rolling_sma: SMA::Indicator::new(parameters.sma_parameters),
            parameters: parameters,
        }
    }

    pub fn update(&mut self, high_price: f64, low_price: f64, close_price: f64) -> f64 {
        let tr_value = self.tr_indicator.update(high_price, low_price, close_price);

        let sma_value = self.rolling_sma.update(tr_value);

        sma_value
    }

    pub fn parameters(&self) -> &Parameters {
        &self.parameters
    }
}
