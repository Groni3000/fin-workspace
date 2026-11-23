//! [`Volume`]: how much traded over an interval.

use std::{
    error::Error,
    fmt::Display,
    iter::Sum,
    ops::{Add, AddAssign},
    str::FromStr,
};

use crate::quantity::Quantity;

/// How much traded over an interval, in the units an order's [`Quantity`] counts (contracts,
/// shares, coins) and with the same decimal places, so a fill's quantity converts without loss.
///
/// Stored as `u128` raw units: sums may outgrow 64 bits.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Volume {
    value: u128,
}

impl Volume {
    pub const PRECISION: u32 = Quantity::PRECISION;
    /// 1e9
    pub const SCALE: u128 = 10_u128.pow(Self::PRECISION);
    pub const ZERO: Self = Self::new(0);

    /// From raw units: `1` is `0.000000001`.
    pub const fn new(value: u128) -> Self {
        Self { value }
    }

    /// Raw units: `1` is `0.000000001`.
    pub const fn value(self) -> u128 {
        self.value
    }

    /// Whole units: contracts, shares.
    pub const fn from_units(units: u64) -> Self {
        Self::new(units as u128 * Self::SCALE)
    }
}

impl From<Quantity> for Volume {
    fn from(qty: Quantity) -> Self {
        Self::new(u128::from(qty.value()))
    }
}

impl Display for Volume {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let int = self.value / Self::SCALE;
        let frac = self.value % Self::SCALE;
        if frac == 0 {
            write!(f, "{int}")
        } else {
            write!(f, "{int}.{}", format!("{frac:09}").trim_end_matches('0'))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseVolumeError {
    /// Anything but digits with at most one dot between them: no sign, no spaces, no exponent.
    InvalidFormat,
    /// More fraction digits than [`Volume::PRECISION`].
    PrecisionError(usize),
    /// Beyond what `u128` raw units hold.
    OutOfBounds,
}

impl Display for ParseVolumeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidFormat => write!(f, "invalid format"),
            Self::PrecisionError(digits) => {
                write!(f, "{digits} fraction digits, at most {}", Volume::PRECISION)
            }
            Self::OutOfBounds => write!(f, "out of bounds"),
        }
    }
}

impl Error for ParseVolumeError {}

impl FromStr for Volume {
    type Err = ParseVolumeError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, ""));
        let has_dot = integer.len() < s.len();
        let all_digits = integer
            .bytes()
            .chain(fraction.bytes())
            .all(|b| b.is_ascii_digit());
        if integer.is_empty() || (has_dot && fraction.is_empty()) || !all_digits {
            return Err(ParseVolumeError::InvalidFormat);
        }
        if fraction.len() > Self::PRECISION as usize {
            return Err(ParseVolumeError::PrecisionError(fraction.len()));
        }

        let digits = |part: &str| {
            part.bytes().try_fold(0_u128, |acc, b| {
                acc.checked_mul(10)?.checked_add(u128::from(b - b'0'))
            })
        };
        let integer = digits(integer).ok_or(ParseVolumeError::OutOfBounds)?;
        let fraction = digits(fraction).expect("at most 9 digits")
            * 10_u128.pow(Self::PRECISION - fraction.len() as u32);

        integer
            .checked_mul(Self::SCALE)
            .and_then(|raw| raw.checked_add(fraction))
            .map(Self::new)
            .ok_or(ParseVolumeError::OutOfBounds)
    }
}

/// Panics on overflow. If you paniced - you've already missed a bug somewhere else.
impl Add for Volume {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self::new(self.value.checked_add(rhs.value).expect("volume overflow"))
    }
}

impl AddAssign for Volume {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sum for Volume {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Add::add)
    }
}

#[cfg(test)]
mod tests;
