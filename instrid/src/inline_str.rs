//! This module is a workaround to bypass
//! runtime deserialization limitations
//!
//! I want Instruments that are:
//!     - stack allocated (aka comptime compatable)
//!     - thus copiable
//!     - de/serializable
//!
//! Unfortunately, I can't deserialize with `&'static str`.
//! Cow<'static, str> will break Copy.
//!
//! But, knowing that there is no base asset names
//! (we call it `AssetSymbol`)
//! longer than 12 chars (at least to my knowledge),
//! we can build our own bounded string representation

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// A comptime bounded string representation
///
/// Note: due to usacase specifics,
/// we have a **limitation of N = 255**
///
/// **Invariants to preserve:**
///     - N <= 255 (u8::MAX)
///     - self.len <= N
///     - self.buffer contains only valid ASCII
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InlineStr<const N: usize> {
    buffer: [u8; N],
    len: u8, // assume N <= 255
}

#[derive(Debug, PartialEq, Eq)]
pub enum InlineStrError {
    TooLong { got: usize, cap: usize },
    NotAscii,
}

impl<const N: usize> InlineStr<N> {
    pub const fn new(code: &str) -> Result<Self, InlineStrError> {
        const { assert!(N <= 255, "N must be <= 255") }
        if code.len() > N {
            return Err(InlineStrError::TooLong {
                got: code.len(),
                cap: N,
            });
        }

        let bytes = code.as_bytes();
        let mut buffer = [0u8; N];
        let mut idx = 0;
        while idx < code.len() {
            let byte = bytes[idx];
            if !byte.is_ascii() {
                return Err(InlineStrError::NotAscii);
            }
            buffer[idx] = bytes[idx];
            idx += 1;
        }

        Ok(Self {
            buffer,
            len: bytes.len() as u8,
        })
    }

    pub const fn as_str(&self) -> &str {
        let ptr_buffer = self.buffer.as_ptr();
        let len = self.len as usize;

        // SOUNDNESS NOTE: the safety of this unsafe block depends on a type-wide
        // invariant — `self.len as usize <= N` and `buffer[0..len]` is valid ASCII.
        // Every safe method on InlineStr must preserve this. Adding a `&mut self`
        // setter that writes `len` or `buffer` without re-checking this invariant
        // makes `as_str` unsound.
        unsafe {
            // SAFETY:
            //      - len <= N - enforced when created
            //      - self.buffer.len() >= self.len - enforced when created
            //      - len is private, no "mut" methods are provided - invariants above can't be broken
            let slice = std::slice::from_raw_parts(ptr_buffer, len);
            // SAFETY:
            //      - self.buffer - valid ASCII < UTF-8
            //      - self.buffer is private, not "mut" methods are provided, invariant can't be broken
            std::str::from_utf8_unchecked(slice)
        }
    }
}

#[cfg(feature = "serde")]
impl<const N: usize> Serialize for InlineStr<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.as_str())
    }
}

#[cfg(feature = "serde")]
impl<'de, const N: usize> Deserialize<'de> for InlineStr<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s: &str = serde::Deserialize::deserialize(deserializer)?;
        Self::new(s).map_err(|e| match e {
            InlineStrError::TooLong { got, cap } => serde::de::Error::custom(format!(
                "string too long: got {got} bytes, capacity {cap}"
            )),
            InlineStrError::NotAscii => serde::de::Error::custom("string contains non-ASCII bytes"),
        })
    }
}
