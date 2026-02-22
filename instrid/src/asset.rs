use std::fmt;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Asset {
    bytes: [u8; 8],
    len: u8,
}

impl Asset {
    /// Creates an Asset from a static string. Should only be used for constants.
    ///
    /// # Panics
    /// Panics at compile time if the code is invalid.
    /// For runtime parsing with proper error handling, use `FromStr` instead:
    /// ```
    /// let asset: Asset = "BTC".parse()?;
    /// ```
    pub const fn new(code: &str) -> Self {
        let src = code.as_bytes();
        let len = src.len();

        assert!(len > 0 && len <= 8, "Asset code must be 1-8 characters");

        let mut bytes = [0u8; 8];
        let mut i = 0;
        while i < len {
            assert!(
                src[i].is_ascii_uppercase(),
                "Asset code must be uppercase ASCII"
            );
            bytes[i] = src[i];
            i += 1;
        }

        Asset {
            bytes,
            len: len as u8,
        }
    }

    /// Creates an asset from a static string without safety checks.
    ///
    const fn new_unchecked(code: &str) -> Self {
        let src = code.as_bytes();
        let mut bytes = [0u8; 8];
        let mut i = 0;
        while i < src.len() {
            bytes[i] = src[i];
            i += 1;
        }
        Asset {
            bytes,
            len: src.len() as u8,
        }
    }

    /// Returns the asset code as a string.
    pub fn code(&self) -> &str {
        // Safety: we only allow valid ASCII uppercase via new() and FromStr
        std::str::from_utf8(&self.bytes[..self.len as usize]).unwrap()
    }

    // Common constants
    pub const USD: Asset = Asset::new("USD");
    pub const EUR: Asset = Asset::new("EUR");
    pub const GBP: Asset = Asset::new("GBP");
    pub const JPY: Asset = Asset::new("JPY");
    pub const BTC: Asset = Asset::new("BTC");
    pub const ETH: Asset = Asset::new("ETH");
    pub const USDT: Asset = Asset::new("USDT");
}

#[derive(Debug)]
pub struct AssetParseError(String);

impl fmt::Display for AssetParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid asset code: '{}' (must be 1-8 uppercase ASCII characters)",
            self.0
        )
    }
}

impl std::error::Error for AssetParseError {}

impl FromStr for Asset {
    type Err = AssetParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let src = s.as_bytes();
        if src.is_empty() || src.len() > 8 || !src.iter().all(|b| b.is_ascii_uppercase()) {
            return Err(AssetParseError(s.to_string()));
        }
        Ok(Asset::new_unchecked(s))
    }
}

impl fmt::Display for Asset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.code())
    }
}
