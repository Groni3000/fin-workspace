use std::array::TryFromSliceError;

/// An ASCII code of fixed length `N` bytes.
///
/// Represents all "code-like" ASCII data with known length at compile time throught crates.
///
/// Examples: `Currency` code, `Mic` code, `Lei` code...
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct AsciiCode<const N: usize> {
    code: [u8; N],
}

impl<const N: usize> AsciiCode<N> {
    pub const fn new(code: [u8; N]) -> Option<Self> {
        if !code.is_ascii() {
            return None;
        };
        Some(Self { code })
    }

    pub const fn code(&self) -> [u8; N] {
        self.code
    }

    pub fn as_str(&self) -> &str {
        // SAFETY: code is validated before construction,
        // not a public field, no `&mut self` methods provided.
        unsafe { str::from_utf8_unchecked(&self.code) }
    }
}

impl<const N: usize> std::fmt::Debug for AsciiCode<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // "{:?}" on a str gives the quoted form: "CNY"
        write!(f, "{:?}", self.as_str())
    }
}

impl<const N: usize> std::fmt::Display for AsciiCode<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl<const N: usize> Default for AsciiCode<N> {
    fn default() -> Self {
        Self { code: [b'?'; N] }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AsciiCodeError {
    WrongLength,
    NotAscii,
}

impl From<TryFromSliceError> for AsciiCodeError {
    fn from(_value: TryFromSliceError) -> Self {
        AsciiCodeError::WrongLength
    }
}

impl std::fmt::Display for AsciiCodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongLength => f.write_str("byte length does not match code width"),
            Self::NotAscii => f.write_str("code contains non-ASCII bytes"),
        }
    }
}

impl std::error::Error for AsciiCodeError {}

impl<const N: usize> TryFrom<&str> for AsciiCode<N> {
    type Error = AsciiCodeError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let bytes: [u8; N] = value.as_bytes().try_into()?;
        Self::new(bytes).ok_or(AsciiCodeError::NotAscii)
    }
}

impl<const N: usize> From<&[u8; N]> for AsciiCode<N> {
    fn from(value: &[u8; N]) -> Self {
        AsciiCode::new(*value).unwrap()
    }
}

impl<const N: usize> TryFrom<&[u8]> for AsciiCode<N> {
    type Error = AsciiCodeError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        let code: [u8; N] = value.try_into()?;
        AsciiCode::new(code).ok_or_else(|| AsciiCodeError::NotAscii)
    }
}
