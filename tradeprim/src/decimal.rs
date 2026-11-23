//! The one decimal format every fixed-point type here parses: `123`, `123.45` and, for a type
//! that can be negative, `-123.45`.

use std::{error::Error, fmt::Display};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseDecimalError {
    /// Anything but digits with at most one dot between them, after an optional `-`: no `+`,
    /// no spaces, no exponent, nothing like `.5` or `5.`. Also a `-` for a type that can't be
    /// negative.
    InvalidFormat,
    /// More fraction digits than the type keeps.
    PrecisionError(usize),
    /// Beyond what the type holds.
    OutOfBounds,
}

impl Display for ParseDecimalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidFormat => write!(f, "invalid format"),
            Self::PrecisionError(digits) => write!(f, "too many fraction digits: {digits}"),
            Self::OutOfBounds => write!(f, "out of bounds"),
        }
    }
}

impl Error for ParseDecimalError {}

/// A parsed decimal: its sign and its absolute value in raw units.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Decimal {
    negative: bool,
    raw: u128,
}

impl Decimal {
    /// For a type that can't be negative: a `-` is `InvalidFormat`, even on zero.
    pub fn unsigned(self) -> Result<u128, ParseDecimalError> {
        match self.negative {
            true => Err(ParseDecimalError::InvalidFormat),
            false => Ok(self.raw),
        }
    }

    pub fn signed(self) -> Result<i128, ParseDecimalError> {
        let raw = i128::try_from(self.raw).map_err(|_| ParseDecimalError::OutOfBounds)?;
        Ok(if self.negative { -raw } else { raw })
    }
}

/// `10^n` for every `n` whose power fits `u64`.
const POW10: [u64; 20] = {
    let mut table = [1_u64; 20];
    let mut n = 1;
    while n < 20 {
        table[n] = table[n - 1] * 10;
        n += 1;
    }
    table
};

/// Parses `s` into raw units with `precision` (at most 19) decimal places: with 9, `"1.5"` is
/// `1_500_000_000`. The caller checks the sign and its own range.
#[inline]
pub fn parse_decimal(s: &str, precision: u32) -> Result<Decimal, ParseDecimalError> {
    debug_assert!(precision <= 19, "precision {precision} past what u64 holds");
    let (negative, unsigned) = match s.as_bytes().split_first() {
        Some((b'-', rest)) => (true, rest),
        _ => (false, s.as_bytes()),
    };
    let (integer, fraction) = match unsigned.iter().position(|&b| b == b'.') {
        Some(dot) => (&unsigned[..dot], Some(&unsigned[dot + 1..])),
        None => (unsigned, None),
    };
    let (Some(int), Some(frac)) = (digits(integer), digits(fraction.unwrap_or_default())) else {
        return Err(ParseDecimalError::InvalidFormat);
    };
    if integer.is_empty() || fraction.is_some_and(<[u8]>::is_empty) {
        return Err(ParseDecimalError::InvalidFormat);
    }
    let fraction_len = fraction.map_or(0, <[u8]>::len);
    if fraction_len > precision as usize {
        return Err(ParseDecimalError::PrecisionError(fraction_len));
    }

    // At most `precision` digits, scaled to `precision`: below 10^19, so it fits `u64`.
    let frac = frac.expect("at most 19 digits") as u64 * POW10[precision as usize - fraction_len];
    let scale = POW10[precision as usize];
    let raw = int
        .and_then(|int| {
            // Most values stay in `u64`; only big ones need `u128`.
            let small = u64::try_from(int)
                .ok()
                .and_then(|int| int.checked_mul(scale)?.checked_add(frac));
            match small {
                Some(raw) => Some(u128::from(raw)),
                None => int
                    .checked_mul(u128::from(scale))?
                    .checked_add(u128::from(frac)),
            }
        })
        .ok_or(ParseDecimalError::OutOfBounds)?;

    Ok(Decimal { negative, raw })
}

/// A run of ASCII digits: `None` if a byte isn't one, `Some(None)` if it doesn't fit `u128`.
fn digits(part: &[u8]) -> Option<Option<u128>> {
    // Up to 19 digits always fit `u64`, whose arithmetic is cheaper than `u128`'s.
    if part.len() <= 19 {
        let mut acc = 0_u64;
        for &b in part {
            let digit = b.wrapping_sub(b'0');
            if digit > 9 {
                return None;
            }
            acc = acc * 10 + u64::from(digit);
        }
        return Some(Some(u128::from(acc)));
    }
    let mut acc = Some(0_u128);
    for &b in part {
        let digit = b.wrapping_sub(b'0');
        if digit > 9 {
            return None;
        }
        acc = acc.and_then(|acc| acc.checked_mul(10)?.checked_add(u128::from(digit)));
    }
    Some(acc)
}

#[cfg(test)]
mod tests;
