#[derive(Debug, Clone, Copy)]
pub struct Parameters {}

/// TR indicator does not have parameters.
///
/// We keep this class for a consistant approach to all indicators.
impl Parameters {
    pub fn new() -> Self {
        Parameters {}
    }
}

/// `True Range` indicator (TR)
///
/// The maximum of 3 values:
///     - (high - low)
///     - (high - previous_close).abs()
///     - (low - previous_close).abs()
///
/// Note: If even one price is invalid (NAN/inf) => indicator resets.
#[derive(Debug)]
pub struct Indicator {
    previous_close: f64,
}
impl Indicator {
    pub fn new(_parameters: Parameters) -> Self {
        Indicator {
            previous_close: f64::NAN,
        }
    }

    #[inline]
    pub fn update(&mut self, high_price: f64, low_price: f64, close_price: f64) -> f64 {
        let h_l = high_price - low_price;
        let h_c = (high_price - self.previous_close).abs();
        let l_c = (low_price - self.previous_close).abs();
        self.previous_close = close_price;

        // This bullshit is because python's pandas
        // `df.max(axis=1, skipna=False)`
        // returns `max(nan, inf) = nan`, `max(nan, finite_float) = nan` ...
        //
        // In rust if one of the values are nan, then OTHER value is returned
        //
        // So, if any value is nan, we return nan like in pandas
        if h_l.is_nan() || h_c.is_nan() || l_c.is_nan() {
            return f64::NAN;
        }

        h_l.max(h_c).max(l_c)
    }
}
