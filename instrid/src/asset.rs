use std::fmt::Display;

/// Represents an asset (e.g., equity, commodity, currency, etc.).
///
/// Asset - an entity that can be traded or cash settled.
///
/// Examples:
///     - AAPL, Equity
///     - USD, Currency
///     - BTC, Currency
///     - S&P 500, Index (cash settled)
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Asset {
    name: &'static str,
    class: AssetClass,
}

impl Asset {
    pub const fn new(name: &'static str, class: AssetClass) -> Self {
        Self { name, class }
    }
    pub fn class(&self) -> AssetClass {
        self.class
    }
}

impl Display for Asset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}){}", self.class, self.name)
    }
}

/// Represents the class or type of an asset (e.g., equity, commodity, currency, etc.).
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssetClass {
    /// Shares, ETFs, REITs - ownership stakes in companies or funds.
    Equity,
    /// Physical goods: energy (crude oil, natural gas), metals (gold, silver),
    /// agriculture (corn, wheat).
    Commodity,
    /// Fiat currencies (USD, EUR) and cryptocurrency (BTC, ETH).
    Currency,
    /// Debt instruments: government bonds, corporate bonds, treasury bills.
    FixedIncome,
    /// Direct property or real estate investment instruments
    /// (excluding REITs which fall under equity).
    RealEstate,
    ///Market indices: S&P 500, NASDAQ Composite, VIX. Not directly tradeable,
    ///but derivatives reference them.
    Index,
}

impl Display for AssetClass {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            AssetClass::Equity => "Equity",
            AssetClass::Commodity => "Commodity",
            AssetClass::Currency => "Currency",
            AssetClass::FixedIncome => "FixedIncome",
            AssetClass::RealEstate => "RealEstate",
            AssetClass::Index => "Index",
        };
        f.write_str(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_asset_new() {
        let name = "AAPL";
        let asset_class = AssetClass::Equity;
        let aapl = Asset::new(name, asset_class);

        assert_eq!(&aapl.name, &name);
        assert_eq!(&aapl.class, &AssetClass::Equity);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_asset_class_serialization() {
        let asset_class = AssetClass::Equity;
        let serialized = serde_json::to_string(&asset_class).expect("expected serializable value");

        assert_eq!(serialized, "\"Equity\"");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_asset_class_deserialization() {
        let serialized = "\"Equity\"";
        let asset_class: AssetClass =
            serde_json::from_str(serialized).expect("expected deserializable value");

        assert_eq!(asset_class, AssetClass::Equity);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_asset_serialization() {
        let asset = Asset::new("USD", AssetClass::Currency);
        let serialized = serde_json::to_string(&asset).expect("expected serializable value");

        assert_eq!(serialized, r#"{"name":"USD","class":"Currency"}"#);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_asset_deserialization() {
        let serialized = r#"{"name":"USD","class":"Currency"}"#;
        // We can deserialize a `&'static str`
        let asset: Asset = serde_json::from_str(serialized).expect("expected deserializable value");

        assert_eq!(asset.name, "USD");
        assert_eq!(asset.class, AssetClass::Currency);
    }

    /// Demonstrates the `&'static str` limitation: deserializing from a
    /// runtime-owned buffer (here a `Vec<u8>`) does not compile, because the
    /// borrow into that buffer is not `'static`.
    #[cfg(feature = "serde")]
    #[test]
    fn test_asset_deserialization_from_runtime_buffer() {
        let bytes: Vec<u8> = br#"{"name":"USD","class":"Currency"}"#.to_vec();
        let owned: String = String::from_utf8(bytes).unwrap();

        // ❌ Uncomment to observe the failure:
        // let asset: Asset = serde_json::from_str(&owned).expect("...");
        //
        // error[E0597]: `owned` does not live long enough
        //   argument requires that `owned` is borrowed for `'static`
        //
        let _ = owned;
        //
        // Cow<'static, str> would work, but we would loose
        // `Copy` for Asset => FuturesContract => We would have
        // a lot of problems with cursor in futchain...
        //
        // Yikes :(
    }
}
