use std::fmt::Display;

use tradeprim::currency::{Currency, CurrencyTag};

use crate::inline_str::InlineStrError;

type AssetName = crate::inline_str::InlineStr<12>;

/// An entity that can be traded or cash settled.
///
/// Each class that has its own variant is built only through it, so one asset has one
/// representation (two spellings of USD would be two different `HashMap` keys):
/// - `Currency`: ISO 4217 only, with the ISO precision. USD, EUR.
/// - `Crypto`: a coin or token, by name. BTC, USDT.
/// - `Other`: a name and a class, for classes without a variant yet. AAPL (equity), CL
///   (commodity), ES (index).
///
/// Serde keeps one shape for every variant, `{"name":"USD","class":"Currency"}`, and reads it
/// back through [`Asset::new`], so a currency is checked against the ISO registry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Asset {
    Currency(CurrencyTag),
    Crypto(AssetName),
    Other(OtherAsset),
}

/// The name and class of an asset whose class has no variant of its own.
///
/// Its fields are private: it is built only by [`Asset::new`] and [`Asset::other`], which never
/// make one for a class that has its own variant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OtherAsset {
    name: AssetName,
    class: AssetClass,
}

impl OtherAsset {
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn class(&self) -> AssetClass {
        self.class
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssetError {
    /// Longer than 12 characters, or not ASCII.
    Name(InlineStrError),
    /// Class `Currency`, but not an ISO 4217 code.
    UnknownCurrency,
    /// [`Asset::other`] with a class that has its own variant.
    HasOwnVariant(AssetClass),
}

impl Display for AssetError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AssetError::Name(e) => write!(f, "invalid asset name: {e}"),
            AssetError::UnknownCurrency => write!(f, "not an ISO 4217 currency"),
            AssetError::HasOwnVariant(class) => {
                write!(f, "class {class} has its own variant, use its constructor")
            }
        }
    }
}

impl std::error::Error for AssetError {}

impl Asset {
    /// Builds the variant `class` belongs to. A `Currency` is looked up in the ISO registry.
    pub fn new(name: &str, class: AssetClass) -> Result<Self, AssetError> {
        match class {
            AssetClass::Currency => Currency::from_alphabetic_code(name)
                .ok()
                .flatten()
                .map(Self::currency)
                .ok_or(AssetError::UnknownCurrency),
            AssetClass::Crypto => Self::crypto(name),
            _ => Self::other(name, class),
        }
    }

    pub const fn currency(currency: Currency) -> Self {
        Self::Currency(currency.tag())
    }

    pub const fn crypto(name: &str) -> Result<Self, AssetError> {
        match AssetName::new(name) {
            Ok(name) => Ok(Self::Crypto(name)),
            Err(e) => Err(AssetError::Name(e)),
        }
    }

    /// For classes without a variant of their own; `const`, unlike [`Asset::new`].
    pub const fn other(name: &str, class: AssetClass) -> Result<Self, AssetError> {
        if matches!(class, AssetClass::Currency | AssetClass::Crypto) {
            return Err(AssetError::HasOwnVariant(class));
        }
        match AssetName::new(name) {
            Ok(name) => Ok(Self::Other(OtherAsset { name, class })),
            Err(e) => Err(AssetError::Name(e)),
        }
    }

    pub fn class(&self) -> AssetClass {
        match self {
            Asset::Currency(_) => AssetClass::Currency,
            Asset::Crypto(_) => AssetClass::Crypto,
            Asset::Other(other) => other.class,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            Asset::Currency(tag) => tag.code(),
            Asset::Crypto(name) => name.as_str(),
            Asset::Other(other) => other.name.as_str(),
        }
    }
}

impl From<Currency> for Asset {
    fn from(currency: Currency) -> Self {
        Self::currency(currency)
    }
}

impl Display for Asset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}|{}", self.class(), self.name())
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Asset {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let mut st = serializer.serialize_struct("Asset", 2)?;
        st.serialize_field("name", self.name())?;
        st.serialize_field("class", &self.class())?;
        st.end()
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Asset {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        #[derive(serde::Deserialize)]
        struct Raw {
            name: AssetName,
            class: AssetClass,
        }
        let raw = Raw::deserialize(deserializer)?;
        Asset::new(raw.name.as_str(), raw.class).map_err(serde::de::Error::custom)
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
    /// Fiat currencies (USD, EUR).
    Currency,
    /// Cryptocurrencies: BTC, ETH, and other digital assets.
    Crypto,
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
            AssetClass::Crypto => "Crypto",
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
    #[cfg(feature = "serde")]
    use crate::_assert_owned;

    #[test]
    fn new_builds_the_variant_of_its_class() {
        let usd = Asset::new("USD", AssetClass::Currency).expect("ISO code");
        let Asset::Currency(tag) = usd else {
            panic!("expected a currency, got {usd:?}")
        };
        assert_eq!(tag.code(), "USD");
        assert_eq!(tag.precision(), 2, "precision comes from the ISO registry");

        let btc = Asset::new("BTC", AssetClass::Crypto).expect("valid name");
        assert!(matches!(btc, Asset::Crypto(name) if name.as_str() == "BTC"));

        let aapl = Asset::new("AAPL", AssetClass::Equity).expect("valid name");
        let Asset::Other(other) = aapl else {
            panic!("expected other, got {aapl:?}")
        };
        assert_eq!((other.name(), other.class()), ("AAPL", AssetClass::Equity));
    }

    #[test]
    fn a_currency_has_one_representation() {
        let looked_up = Asset::new("USD", AssetClass::Currency).expect("ISO code");
        assert_eq!(looked_up, Asset::currency(Currency::usd()));
        assert_eq!(looked_up, Asset::from(Currency::usd()));
        assert_eq!(
            Asset::other("USD", AssetClass::Currency),
            Err(AssetError::HasOwnVariant(AssetClass::Currency))
        );
        assert_eq!(
            Asset::other("BTC", AssetClass::Crypto),
            Err(AssetError::HasOwnVariant(AssetClass::Crypto))
        );
    }

    #[test]
    fn a_currency_outside_the_iso_registry_is_rejected() {
        assert_eq!(
            Asset::new("USDT", AssetClass::Currency),
            Err(AssetError::UnknownCurrency)
        );
        assert_eq!(
            Asset::new("ZZZ", AssetClass::Currency),
            Err(AssetError::UnknownCurrency)
        );
    }

    #[test]
    fn class_name_and_display() {
        let cases = [
            (
                Asset::currency(Currency::eur()),
                AssetClass::Currency,
                "EUR",
                "Currency|EUR",
            ),
            (
                Asset::crypto("USDT").expect("valid"),
                AssetClass::Crypto,
                "USDT",
                "Crypto|USDT",
            ),
            (
                Asset::other("ES", AssetClass::Index).expect("valid"),
                AssetClass::Index,
                "ES",
                "Index|ES",
            ),
        ];
        for (asset, class, name, display) in cases {
            assert_eq!(asset.class(), class);
            assert_eq!(asset.name(), name);
            assert_eq!(asset.to_string(), display);
        }
    }

    #[test]
    fn a_name_longer_than_12_is_rejected() {
        assert_eq!(
            Asset::crypto("ABCDEFGHIJKLM"),
            Err(AssetError::Name(InlineStrError::TooLong {
                got: 13,
                cap: 12
            }))
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn asset_class_serde() {
        assert_eq!(
            serde_json::to_string(&AssetClass::Equity).expect("serializable"),
            "\"Equity\""
        );
        let class: AssetClass = serde_json::from_str("\"Equity\"").expect("deserializable");
        assert_eq!(class, AssetClass::Equity);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn every_variant_serializes_to_name_and_class() {
        let cases = [
            (
                Asset::currency(Currency::usd()),
                r#"{"name":"USD","class":"Currency"}"#,
            ),
            (
                Asset::crypto("BTC").expect("valid"),
                r#"{"name":"BTC","class":"Crypto"}"#,
            ),
            (
                Asset::other("AAPL", AssetClass::Equity).expect("valid"),
                r#"{"name":"AAPL","class":"Equity"}"#,
            ),
        ];
        for (asset, json) in cases {
            assert_eq!(serde_json::to_string(&asset).expect("serializable"), json);
            let back: Asset = serde_json::from_str(json).expect("deserializable");
            assert_eq!(back, asset);
        }
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserializing_a_currency_restores_its_precision() {
        let jpy: Asset =
            serde_json::from_str(r#"{"name":"JPY","class":"Currency"}"#).expect("ISO code");
        let Asset::Currency(tag) = jpy else {
            panic!("expected a currency, got {jpy:?}")
        };
        assert_eq!(tag.precision(), 0);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserializing_a_currency_outside_the_iso_registry_fails() {
        let err = serde_json::from_str::<Asset>(r#"{"name":"USDT","class":"Currency"}"#)
            .expect_err("USDT is not ISO 4217");
        assert_eq!(err.to_string(), "not an ISO 4217 currency");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_asset_is_owned() {
        _assert_owned::<Asset>();
    }
}
