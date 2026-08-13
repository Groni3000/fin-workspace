use std::{collections::VecDeque, f64};

use pyo3::{exceptions::PyValueError, pyclass, pymethods, PyResult};

#[pyclass]
#[derive(Clone)]
pub struct Parameters {
    /// Relatively large type to support high frequency periods like week in seconds.
    period: u32,
}

#[pymethods]
impl Parameters {
    #[new]
    pub fn new(period: u32) -> PyResult<Self> {
        if period <= 0 {
            return Err(PyValueError::new_err("Period should be positive."));
        }
        Ok(Self { period })
    }
}

#[pyclass]
pub struct Indicator {
    // TODO: change to `period`
    parameters: Parameters,
    values: VecDeque<f64>,
}
#[pymethods]
impl Indicator {
    #[new]
    // TODO: change to reference, Indicator should initiate `period`
    pub fn new(parameters: Parameters) -> Self {
        let values = VecDeque::with_capacity(parameters.period.clone() as usize);

        Self { parameters, values }
    }

    /// Calculates Percent Rank of a `new_value`
    ///
    /// Any non-finite value is treated as NAN and resets the indicator.
    pub fn update(&mut self, price: f64) -> f64 {
        if !price.is_finite() {
            self.reset();

            return f64::NAN;
        }

        if self.values.len() != (self.parameters.period.saturating_sub(1)) as usize {
            self.values.push_back(price);

            return f64::NAN;
        }

        let n_of_lte_elements = self
            .values
            .iter()
            .fold(0 as u32, |acc, x| match x <= &price {
                true => acc + 1,
                false => acc,
            });
        self.values.push_back(price);
        self.values.pop_front();

        100.0 * (n_of_lte_elements + 1) as f64 / self.parameters.period as f64
    }

    pub fn reset(&mut self) {
        self.values.clear();
    }
}
