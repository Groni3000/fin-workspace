use crate::{sma, tr};

#[derive(Debug, Clone, Copy)]
pub struct Parameters {
    tr_parameters: tr::Parameters,
    sma_parameters: sma::Parameters,
}

impl Parameters {
    pub fn new(tr_parameters: tr::Parameters, sma_parameters: sma::Parameters) -> Self {
        Parameters {
            tr_parameters,
            sma_parameters,
        }
    }

    pub fn tr_parameters(&self) -> tr::Parameters {
        self.tr_parameters
    }

    pub fn sma_parameters(&self) -> sma::Parameters {
        self.sma_parameters
    }
}

#[derive(Debug)]
pub struct Indicator {
    tr_indicator: tr::Indicator,
    rolling_sma: sma::Indicator,
    parameters: Parameters,
}

impl Indicator {
    pub fn new(parameters: Parameters) -> Self {
        Indicator {
            tr_indicator: tr::Indicator::new(parameters.tr_parameters),
            rolling_sma: sma::Indicator::new(parameters.sma_parameters),
            parameters,
        }
    }

    pub fn update(&mut self, high_price: f64, low_price: f64, close_price: f64) -> f64 {
        let tr_value = self.tr_indicator.update(high_price, low_price, close_price);

        self.rolling_sma.update(tr_value)
    }

    pub fn parameters(&self) -> &Parameters {
        &self.parameters
    }
}
