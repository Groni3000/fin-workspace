use std::collections::VecDeque;

/// Parameters for configuring a Simple Moving Average (SMA) indicator.
#[derive(Debug, Clone, Copy)]
pub struct Parameters {
    period: usize,
}

impl Parameters {
    /// Creates a new Parameters instance with the specified period.
    ///
    /// # Arguments
    /// * `period` - The window size for the SMA. Must be at least 1.
    ///
    /// # Errors
    /// Returns an error if period is 0.
    pub fn new(period: usize) -> Result<Self, String> {
        if period == 0 {
            return Err("Period for SMA must be at least 1".into());
        }
        Ok(Parameters { period })
    }

    /// Returns the period value.
    ///
    /// # Returns
    /// The period as a usize.
    pub fn get_period(&self) -> usize {
        self.period
    }
}

/// Represents a Simple Moving Average (SMA) indicator that computes incrementally.
///
/// Maintains a sliding window of prices to efficiently update the average.
///
/// # Fields
/// * `period` - The window size for the SMA.
/// * `values` - Deque holding the recent prices in the window.
/// * `sum` - Running sum of the values in the window.
pub struct Indicator {
    parameters: Parameters,
    values: VecDeque<f64>,
    sum: f64,
}

impl Indicator {
    /// Creates a new SMA Indicator with the given parameters.
    ///
    /// # Arguments
    /// * `parameters` - Reference to Parameters containing the period.
    ///
    /// # Returns
    /// A new Indicator instance initialized with an empty window and sum of 0.0.
    pub fn new(parameters: Parameters) -> Self {
        Indicator {
            values: VecDeque::with_capacity(parameters.get_period()),
            parameters,
            sum: 0.0,
        }
    }

    /// Updates the indicator with a new price and returns the current SMA.
    ///
    /// During the initial warm-up period (first `period` updates), returns NaN.
    /// After that, maintains a sliding window and computes the average.
    ///
    /// # Arguments
    /// * `price` - The new price to add to the window.
    ///
    /// # Returns
    /// The current SMA value as f64 (NaN during warm-up).
    pub fn update(&mut self, price: f64) -> f64 {
        // Replicate pandas behavior for NaN and infinity
        if price.is_nan() || price.is_infinite() {
            self.values.clear();
            self.sum = 0.0;

            return f64::NAN;
        }
        if self.values.len() < self.parameters.period {
            self.values.push_back(price);
            self.sum += price;

            if self.values.len() == self.parameters.period {
                return self.sum / self.parameters.period as f64;
            }
            return f64::NAN;
        }
        self.sum -= self.values.pop_front().unwrap_or(0.0);
        self.values.push_back(price);
        self.sum += price;

        self.sum / self.parameters.period as f64
    }

    pub(crate) fn clear(&mut self) {
        self.values.clear();
        self.sum = 0.0;
    }

    pub fn parameters(&self) -> Parameters {
        self.parameters
    }
}

//
// This implementation use Vec instead of VecDeque. Which, in theory, should be faster
// but in practice it is irrelevant due to Python's overhead.
//
// Considering that VecDeque implementation is more readable,
// I decided to use it, instead of Vec.
// But the Vec version is here, commented, just in case.
//
// #[pyclass]
// pub struct Indicator {
//     period: usize,
//     head: usize,      // next write position
//     count: usize,     // how many valid samples (≤ period)
//     buffer: Vec<f64>, // length = period, never reallocates
//     sum: f64,
// }

// #[pymethods]
// impl Indicator {
//     #[new]
//     pub fn new(parameters: &Parameters) -> Self {
//         let period = parameters.period;
//         Self {
//             period,
//             head: 0,
//             count: 0,
//             buffer: vec![0.0; period],
//             sum: 0.0,
//         }
//     }

//     /// Update with a new price and return the current SMA.
//     pub fn update(&mut self, price: f64) -> f64 {
//         if price.is_nan() || price.is_infinite() {
//             // pandas behaviour: invalidate whole window
//             self.count = 0;
//             self.head = 0;
//             self.sum = 0.0;
//             return f64::NAN;
//         }

//         let old = if self.count < self.period {
//             self.count += 1;
//             0.0
//         } else {
//             self.buffer[self.head]
//         };

//         self.sum = self.sum - old + price;
//         self.buffer[self.head] = price;
//         self.head = (self.head + 1) % self.period;

//         if self.count < self.period {
//             f64::NAN
//         } else {
//             self.sum / self.period as f64
//         }
//     }

//     pub fn clear(&mut self) {
//         self.head = 0;
//         self.count = 0;
//         self.sum = 0.0;
//     }
// }
