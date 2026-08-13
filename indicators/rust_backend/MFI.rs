use pyo3::{exceptions::PyValueError, prelude::*, PyResult};
use std::{
    collections::VecDeque,
    ops::{Add, Div, Mul, Sub},
};

#[pyclass]
pub struct Parameters {
    period: usize,
}

#[pymethods]
impl Parameters {
    #[new]
    fn new(period: usize) -> PyResult<Self> {
        if period == 0 {
            return Err(PyValueError::new_err("Period must be >= 1."));
        }
        Ok(Parameters { period })
    }

    #[getter]
    fn period(&self) -> usize {
        self.period
    }
}
// TODO: into `utils.rs`?
#[derive(Clone, Copy)]
pub struct Price(f64);

impl Price {
    pub fn from_f64(value: f64) -> Option<Price> {
        if value.is_finite() {
            Some(Price(value))
        } else {
            None
        }
    }
}

impl Add for Price {
    type Output = Price;

    fn add(self, rhs: Self) -> Self::Output {
        Price {
            0: self.0.add(rhs.0),
        }
    }
}

impl Sub for Price {
    type Output = Price;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            0: self.0.sub(rhs.0),
        }
    }
}

impl Mul<f64> for Price {
    type Output = f64;

    fn mul(self, rhs: f64) -> Self::Output {
        self.0 * rhs
    }
}

// Impl Div by f64 for Price:
impl Div<f64> for Price {
    type Output = Price;

    fn div(self, rhs: f64) -> Self::Output {
        Self { 0: self.0.div(rhs) }
    }
}

/// A rolling sum of a given period.
///
struct RollingSum {
    values: VecDeque<f64>,
    sum: f64,
    warmup_counter: usize,
    period: usize,
}

impl RollingSum {
    pub fn new(period: usize) -> Self {
        let values = VecDeque::with_capacity(period);
        RollingSum {
            values,
            sum: 0.0,
            warmup_counter: 0,
            period,
        }
    }

    /// Update the rolling sum with a new value.
    ///
    /// It assumes that the value is finite. Because this struct works in pair with `Indicator.update()`
    ///
    /// And it converts the value to `Price` beforehand, it is safe to assume that the value is finite.
    ///
    pub fn update(&mut self, value: f64) -> f64 {
        if self.warmup_counter < self.period {
            self.warmup_counter += 1;
            self.sum += value;
            self.values.push_back(value);

            if self.period == self.warmup_counter {
                return self.sum;
            }

            return f64::NAN;
        }

        let old_value = self.values.pop_front().unwrap();
        self.sum -= old_value;
        self.sum += value;
        self.values.push_back(value);

        self.sum
    }

    fn clear(&mut self) {
        self.values.clear();
        self.sum = 0.0;
        self.warmup_counter = 0;
    }
}

#[pyclass]
pub struct Indicator {
    last_typical_price: Option<Price>,
    positive_rolling_sum: RollingSum,
    negative_rolling_sum: RollingSum,
}

#[pymethods]
impl Indicator {
    #[new]
    pub fn new(parameters: &Parameters) -> Self {
        Indicator {
            last_typical_price: None,
            positive_rolling_sum: RollingSum::new(parameters.period()),
            negative_rolling_sum: RollingSum::new(parameters.period()),
        }
    }

    #[inline]
    fn reset(&mut self) {
        self.positive_rolling_sum.clear();
        self.negative_rolling_sum.clear();
        self.last_typical_price = None;
    }

    /// Update the MFI with a new value.
    ///
    #[pyo3(text_signature = "(high_price, low_price, close_price, volume)")]
    pub fn update(&mut self, high: f64, low: f64, close: f64, volume: usize) -> f64 {
        // Convert to Prices with early return if any problem is found.
        let high = match Price::from_f64(high) {
            Some(price) => price,
            None => {
                self.reset();
                return f64::NAN;
            }
        };
        let low = match Price::from_f64(low) {
            Some(price) => price,
            None => {
                self.reset();
                return f64::NAN;
            }
        };
        let close = match Price::from_f64(close) {
            Some(price) => price,
            None => {
                self.reset();
                return f64::NAN;
            }
        };
        // Find typical price. Refresh if it is first update.
        let typical_price = (high + low + close) / 3.0;
        if self.last_typical_price.is_none() {
            self.last_typical_price = Some(typical_price);

            return f64::NAN;
        }

        let diff = (typical_price - self.last_typical_price.unwrap()) * volume as f64;
        self.last_typical_price = Some(typical_price);
        let (pos_roll, neg_roll) = if diff > 0.0 {
            (
                self.positive_rolling_sum.update(diff),
                self.negative_rolling_sum.update(0.0),
            )
        } else {
            (
                self.positive_rolling_sum.update(0.0),
                self.negative_rolling_sum.update(diff),
            )
        };

        if pos_roll.is_nan() || neg_roll.is_nan() {
            return f64::NAN;
        }

        100.0 - 100.0 / (1.0 + (pos_roll / neg_roll).abs())
    }
}

#[cfg(test)]
mod tests {
    use std::f64;

    use super::*;

    #[test]
    fn test_rolling_sum() {
        let mut rolling_sum = RollingSum::new(3);

        assert_eq!(rolling_sum.update(10.0).is_nan(), true);
        assert_eq!(rolling_sum.update(20.0).is_nan(), true);
        assert_eq!(rolling_sum.update(30.0), 60.0);
        assert_eq!(rolling_sum.update(40.0), 90.0);
        assert_eq!(rolling_sum.update(50.0), 120.0);
        assert_eq!(rolling_sum.update(60.0), 150.0);
        assert_eq!(rolling_sum.update(70.0), 180.0);
        assert_eq!(rolling_sum.update(80.0), 210.0);
    }

    #[test]
    fn test_indicator() {
        /*
        * SAMPLE_HIGH_SERIES = pd.Series([105.0, 106.0, 110.0, 109.0, 109.0])
        * SAMPLE_LOW_SERIES = pd.Series([100.0, 93.0, 106.0, 107.0, 108.0])
        * SAMPLE_CLOSE_SERIES = pd.Series([103.0, 94.0, 109.0, 108.0, 107.0])
        * SAMPLE_VOLUME_SERIES = pd.Series([50_000, 140_000, 200_000, 35_000, 20_000])

        * Expected:
        * mfi = pd.Series([np.nan, np.nan, 75.29411764705881, 99.45609945609947, 0.0])
        */
        let prices = vec![
            (105.0, 100.0, 103.0, 50_000),
            (106.0, 93.0, 94.0, 140_000),
            (110.0, 106.0, 109.0, 200_000),
            (109.0, 107.0, 108.0, 35_000),
            (109.0, 108.0, 107.0, 20_000),
        ];

        let expected_values = vec![
            f64::NAN,
            f64::NAN,
            75.29411764705881,
            99.45609945609947,
            0.0,
        ];
        let mut indicator = Indicator::new(&Parameters { period: 2 });

        prices
            .into_iter()
            .zip(expected_values.into_iter())
            .for_each(|((high, low, close, volume), expected_mfi)| {
                if expected_mfi.is_nan() {
                    assert!(indicator.update(high, low, close, volume).is_nan());
                    return;
                }
                assert_eq!(indicator.update(high, low, close, volume), expected_mfi);
            });
    }

    #[test]
    fn test_indicator_reset() {
        /*
        * SAMPLE_HIGH_SERIES = pd.Series([105.0, 106.0, 110.0, 109.0, 109.0])
        * SAMPLE_LOW_SERIES = pd.Series([100.0, 93.0, 106.0, 107.0, 108.0])
        * SAMPLE_CLOSE_SERIES = pd.Series([103.0, 94.0, 109.0, 108.0, 107.0])
        * SAMPLE_VOLUME_SERIES = pd.Series([50_000, 140_000, 200_000, 35_000, 20_000])

        * Expected:
        * mfi = pd.Series([np.nan, np.nan, 75.29411764705881, 99.45609945609947, 0.0])
        */
        let prices = vec![
            (105.0, 100.0, 103.0, 50_000),
            (106.0, 93.0, 94.0, 140_000),
            (110.0, 106.0, 109.0, 200_000),
            (109.0, 107.0, 108.0, 35_000),
            (109.0, 108.0, 107.0, 20_000),
            // Below is a reset.
            (f64::NAN, 108.0, 107.0, 20_000),
            //
            (105.0, 100.0, 103.0, 50_000),
            (106.0, 93.0, 94.0, 140_000),
            (110.0, 106.0, 109.0, 200_000),
            (109.0, 107.0, 108.0, 35_000),
            (109.0, 108.0, 107.0, 20_000),
        ];

        let expected_values = vec![
            f64::NAN,
            f64::NAN,
            75.29411764705881,
            99.45609945609947,
            0.0,
            f64::NAN,
            f64::NAN,
            f64::NAN,
            75.29411764705881,
            99.45609945609947,
            0.0,
        ];
        let mut indicator = Indicator::new(&Parameters { period: 2 });

        prices
            .into_iter()
            .zip(expected_values.into_iter())
            .for_each(|((high, low, close, volume), expected_mfi)| {
                if expected_mfi.is_nan() {
                    assert!(indicator.update(high, low, close, volume).is_nan());
                    return;
                }
                assert_eq!(indicator.update(high, low, close, volume), expected_mfi);
            });

        // Now check with Inf and -Inf.
        let prices = vec![
            (105.0, 100.0, 103.0, 50_000),
            (106.0, 93.0, 94.0, 140_000),
            (110.0, 106.0, 109.0, 200_000),
            (109.0, 107.0, 108.0, 35_000),
            (109.0, 108.0, 107.0, 20_000),
            // Below is a reset.
            (f64::INFINITY, 108.0, 107.0, 20_000),
            //
            (105.0, 100.0, 103.0, 50_000),
            (106.0, 93.0, 94.0, 140_000),
            (110.0, 106.0, 109.0, 200_000),
            (109.0, 107.0, 108.0, 35_000),
            (109.0, 108.0, 107.0, 20_000),
            // Below is a reset.
            (f64::NEG_INFINITY, 108.0, 107.0, 20_000),
            //
            (105.0, 100.0, 103.0, 50_000),
            (106.0, 93.0, 94.0, 140_000),
            (110.0, 106.0, 109.0, 200_000),
            (109.0, 107.0, 108.0, 35_000),
            (109.0, 108.0, 107.0, 20_000),
        ];

        let expected_values = vec![
            f64::NAN,
            f64::NAN,
            75.29411764705881,
            99.45609945609947,
            0.0,
            f64::NAN,
            f64::NAN,
            f64::NAN,
            75.29411764705881,
            99.45609945609947,
            0.0,
            f64::NAN,
            f64::NAN,
            f64::NAN,
            75.29411764705881,
            99.45609945609947,
            0.0,
        ];
        let mut indicator = Indicator::new(&Parameters { period: 2 });

        prices
            .into_iter()
            .zip(expected_values.into_iter())
            .for_each(|((high, low, close, volume), expected_mfi)| {
                if expected_mfi.is_nan() {
                    assert!(indicator.update(high, low, close, volume).is_nan());
                    return;
                }
                assert_eq!(indicator.update(high, low, close, volume), expected_mfi);
            });
    }
}
