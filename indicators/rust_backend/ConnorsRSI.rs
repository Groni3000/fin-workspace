use pyo3::{pyclass, pymethods};

use crate::rust_backend::{Streak, PR, RSI};

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    #[allow(dead_code)]
    streak_parameters: Streak::Parameters,
    rsi_streak_parameters: RSI::Parameters,
    rsi_parameters: RSI::Parameters,
    percent_rank_parameters: PR::Parameters,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(
        streak_parameters: Streak::Parameters,
        rsi_streak_parameters: RSI::Parameters,
        rsi_parameters: RSI::Parameters,
        percent_rank_parameters: PR::Parameters,
    ) -> Self {
        Parameters {
            streak_parameters,
            rsi_streak_parameters,
            rsi_parameters,
            percent_rank_parameters,
        }
    }
}

#[pyclass]
pub struct Indicator {
    streak_indicator: Streak::Indicator,
    rsi_streak_indicator: RSI::Indicator,
    rsi_indicator: RSI::Indicator,
    percent_rank_indicator: PR::Indicator,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: Parameters) -> Self {
        let streak_indicator = Streak::Indicator::new(Streak::Parameters::new());
        let rsi_streak_indicator = RSI::Indicator::new(&parameters.rsi_streak_parameters);
        let rsi_indicator = RSI::Indicator::new(&parameters.rsi_parameters);
        let percent_rank_indicator = PR::Indicator::new(parameters.percent_rank_parameters.clone());

        Indicator {
            streak_indicator,
            rsi_streak_indicator,
            rsi_indicator,
            percent_rank_indicator,
        }
    }

    pub fn update(&mut self, price: f64) -> f64 {
        let streak = self.streak_indicator.update(price);
        let rsi_streak = self.rsi_streak_indicator.update(streak as f64);
        let rsi = self.rsi_indicator.update(price);
        let percent_rank = self.percent_rank_indicator.update(price);

        (rsi_streak + rsi + percent_rank) / 3.0
    }
}
