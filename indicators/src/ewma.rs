/*
Pandas equivalent for stream processing. With parameters:
    1. alpha - smoothing factor (0 < alpha <= 1).
    2. adjust = False
    3. ignore_na = True

If I would implement adjust = False, ignore_na = False, I would need to:
    1. Track number of NaNs occurred.
    2. Implicitly normalize weights when new valid samples occur. So the formula would be
        y_n =   (
                    (1 - alpha) ** number_of_nans * y_(n-1) + alpha * x_n
                )
                    /
                (
                    (1 - alpha) ** number_of_nans + alpha
                )

So, naturally, I would prefer not allowing NaNs/infinitys in input.
And if that's the case, I would invalidate the indicator.
But I'm replicating pandas behavior, so I'm forced to allow NaNs, but chose to ignore them.
*/

/// Parameters for configuring an Exponential Weighted Moving Average (EWMA) indicator.
#[derive(Debug, Clone, Copy)]
pub struct Parameters {
    alpha: f64,
    warmup_samples: usize,
}

impl Parameters {
    /// Creates a new Parameters instance.
    ///
    /// May return error if:
    /// * `warmup_samples` is 0
    /// * `alpha` is not in (0, 1]
    pub fn new(alpha: f64, warmup_samples: usize) -> Result<Self, String> {
        if warmup_samples == 0 {
            return Err("Invalid `warmup_sample`. Must be at least 1.".into());
        }
        if alpha <= 0.0 || alpha > 1.0 {
            return Err("Invalid `alpha`. Must be in (0, 1].".into());
        }

        Ok(Parameters {
            alpha,
            warmup_samples,
        })
    }

    pub fn warmup_samples(&self) -> usize {
        self.warmup_samples
    }

    pub fn alpha(&self) -> f64 {
        self.alpha
    }
}

pub struct Indicator {
    parameters: Parameters,
    beta: f64,
    warmup_counter: usize,
    previous_value: f64,
}

impl Indicator {
    pub fn new(parameters: Parameters) -> Self {
        Indicator {
            parameters,
            beta: 1.0 - parameters.alpha(),
            warmup_counter: 0,
            previous_value: f64::NAN,
        }
    }

    #[inline]
    pub fn update(&mut self, price: f64) -> f64 {
        // We ignore NaNs/infinities, it doesn't count to the `warmup_counter`
        if !price.is_finite() {
            if self.warmup_counter < self.parameters.warmup_samples {
                return f64::NAN;
            }
            return self.previous_value;
        }

        // Warmup process.
        if self.warmup_counter < self.parameters.warmup_samples {
            self.warmup_counter += 1;
            // If it is the first sample
            if self.warmup_counter == 1 {
                // We store initial y_0 = x_0
                self.previous_value = price;
                // If it is the only sample we need - return it.
                if self.parameters.warmup_samples == 1 {
                    return self.previous_value;
                }
            }
            if self.warmup_counter != self.parameters.warmup_samples {
                let new_value = self.parameters.alpha * price + self.beta * self.previous_value;
                self.previous_value = new_value;

                return f64::NAN;
            }
        }
        // If it's the last sample in warmup or just a regular sample
        // we calculate a new value.
        let new_value = self.parameters.alpha * price + self.beta * self.previous_value;

        self.previous_value = new_value;

        new_value
    }

    pub fn parameters(&self) -> Parameters {
        self.parameters
    }
}
