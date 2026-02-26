use std::fmt;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Exchange {
    bytes: [u8; 8],
    len: u8,
}

impl Exchange {
    /// Creates an Exchange from a static string. Should only be used for constants.
    ///
    /// # Panics
    /// Panics at compile time if the code is invalid.
    /// For runtime parsing with proper error handling, use `FromStr` instead:
    /// ```
    /// use instrid::exchange::Exchange;
    /// let exchange: Exchange = "CME".parse().unwrap();
    /// ```
    pub const fn new(code: &str) -> Self {
        let src = code.as_bytes();
        let len = src.len();

        assert!(len > 0 && len <= 8, "Exchange code must be 1-8 characters");

        let mut bytes = [0u8; 8];
        let mut i = 0;
        while i < len {
            assert!(
                src[i].is_ascii_uppercase(),
                "Exchange code must be uppercase ASCII"
            );
            bytes[i] = src[i];
            i += 1;
        }

        Exchange {
            bytes,
            len: len as u8,
        }
    }

    const fn new_unchecked(code: &str) -> Self {
        let src = code.as_bytes();
        let mut bytes = [0u8; 8];
        let mut i = 0;
        while i < src.len() {
            bytes[i] = src[i];
            i += 1;
        }
        Exchange {
            bytes,
            len: src.len() as u8,
        }
    }

    pub fn code(&self) -> &str {
        std::str::from_utf8(&self.bytes[..self.len as usize]).unwrap()
    }

    pub const CME: Exchange = Exchange::new("CME");
    pub const CBOT: Exchange = Exchange::new("CBOT");
    pub const NYMEX: Exchange = Exchange::new("NYMEX");
    pub const NASDAQ: Exchange = Exchange::new("NASDAQ");
    pub const NYSE: Exchange = Exchange::new("NYSE");
    pub const BINANCE: Exchange = Exchange::new("BINANCE");
}

#[derive(Debug)]
pub struct ExchangeParseError(String);

impl fmt::Display for ExchangeParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid exchange code: '{}' (must be 1-8 uppercase ASCII characters)",
            self.0
        )
    }
}

impl std::error::Error for ExchangeParseError {}

impl FromStr for Exchange {
    type Err = ExchangeParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let src = s.as_bytes();
        if src.is_empty() || src.len() > 8 || !src.iter().all(|b| b.is_ascii_uppercase()) {
            return Err(ExchangeParseError(s.to_string()));
        }
        Ok(Exchange::new_unchecked(s))
    }
}

impl fmt::Display for Exchange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.code())
    }
}
