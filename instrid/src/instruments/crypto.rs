use std::fmt::Display;

use crate::asset::Asset;
use crate::instruments::TradedInstrument;
use crate::mic::Mic;

/// A crypto spot pair: BTC/USDT, ETH/BTC, BTC/EUR, EUR/USDT.
///
/// At least one side is an [`Asset::Crypto`]. Spot settles in the quote, so there is no
/// settlement field. A venue without an ISO 10383 code uses [`Mic::xxxx`] ("no market").
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
// `remote = "Self"`: the generated impls are inherent functions, so the trait impls below can
// check the invariant through `new`.
#[cfg_attr(feature = "serde", serde(remote = "Self"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Crypto {
    base: Asset,
    price_quotation: Asset,
    mic: Mic,
}

/// Neither side of a [`Crypto`] pair is an [`Asset::Crypto`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NoCryptoAsset {
    pub base: Asset,
    pub price_quotation: Asset,
}

impl Display for NoCryptoAsset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "a crypto pair needs a crypto asset on one side: {}/{}",
            self.base, self.price_quotation
        )
    }
}

impl std::error::Error for NoCryptoAsset {}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for Crypto {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let raw = Crypto::deserialize(deserializer)?;
        Self::new(raw.base, raw.price_quotation, raw.mic).map_err(serde::de::Error::custom)
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for Crypto {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        Crypto::serialize(self, serializer)
    }
}

impl Crypto {
    pub const fn new(base: Asset, price_quotation: Asset, mic: Mic) -> Result<Self, NoCryptoAsset> {
        if !matches!(base, Asset::Crypto(_)) && !matches!(price_quotation, Asset::Crypto(_)) {
            return Err(NoCryptoAsset {
                base,
                price_quotation,
            });
        }
        Ok(Self {
            base,
            price_quotation,
            mic,
        })
    }

    pub fn base(&self) -> &Asset {
        &self.base
    }

    pub fn price_quotation(&self) -> &Asset {
        &self.price_quotation
    }

    pub fn mic(&self) -> &Mic {
        &self.mic
    }

    /// The quote: spot settles in it.
    pub fn settlement(&self) -> &Asset {
        &self.price_quotation
    }
}

impl TradedInstrument for Crypto {
    fn base(&self) -> &Asset {
        &self.base
    }

    fn price_quotation(&self) -> &Asset {
        &self.price_quotation
    }

    fn mic(&self) -> &Mic {
        &self.mic
    }

    fn settlement(&self) -> &Asset {
        Crypto::settlement(self)
    }
}

impl Display for Crypto {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Crypto:{}/{}@{}",
            self.base, self.price_quotation, self.mic
        )
    }
}

#[cfg(test)]
mod tests {
    use tradeprim::currency::Currency;

    #[cfg(feature = "serde")]
    use crate::_assert_owned;
    use crate::instruments::Instrument;

    use super::*;

    fn crypto(name: &str) -> Asset {
        Asset::crypto(name).expect("valid name")
    }

    fn btc_usdt() -> Crypto {
        Crypto::new(crypto("BTC"), crypto("USDT"), Mic::xxxx()).expect("both sides are crypto")
    }

    #[test]
    fn display() {
        assert_eq!(btc_usdt().to_string(), "Crypto:Crypto|BTC/Crypto|USDT@XXXX");
        assert_eq!(
            Instrument::from(btc_usdt()).to_string(),
            "Crypto:Crypto|BTC/Crypto|USDT@XXXX"
        );
    }

    #[test]
    fn settles_in_the_quote() {
        assert_eq!(btc_usdt().settlement(), &crypto("USDT"));

        let btc_eur = Crypto::new(crypto("BTC"), Currency::eur().into(), Mic::xxxx())
            .expect("the base is crypto");
        assert_eq!(
            Instrument::from(btc_eur).settlement(),
            &Asset::currency(Currency::eur())
        );
    }

    /// Binance lists EURUSDT: fiat base, crypto quote.
    #[test]
    fn a_fiat_base_is_allowed() {
        let eur_usdt = Crypto::new(Currency::eur().into(), crypto("USDT"), Mic::xxxx())
            .expect("the quote is crypto");
        assert_eq!(eur_usdt.to_string(), "Crypto:Currency|EUR/Crypto|USDT@XXXX");
    }

    #[test]
    fn a_pair_without_a_crypto_side_is_rejected() {
        let eur = Asset::currency(Currency::eur());
        let usd = Asset::currency(Currency::usd());
        assert_eq!(
            Crypto::new(eur, usd, Mic::xxxx()),
            Err(NoCryptoAsset {
                base: eur,
                price_quotation: usd
            })
        );
        let aapl = Asset::equity("AAPL").expect("valid name");
        let err = Crypto::new(aapl, usd, Mic::xnas()).expect_err("no crypto side");
        assert_eq!(
            err.to_string(),
            "a crypto pair needs a crypto asset on one side: Equity|AAPL/Currency|USD"
        );
    }

    #[cfg(feature = "serde")]
    const BTC_USDT_JSON: &str = r#"{"type":"Crypto","base":{"name":"BTC","class":"Crypto"},"price_quotation":{"name":"USDT","class":"Crypto"},"mic":"XXXX"}"#;

    #[cfg(feature = "serde")]
    #[test]
    fn serde_round_trip_through_instrument() {
        let instrument = Instrument::from(btc_usdt());
        let json = serde_json::to_string(&instrument).expect("serializable");
        assert_eq!(json, BTC_USDT_JSON);
        let back: Instrument = serde_json::from_str(BTC_USDT_JSON).expect("deserializable");
        assert_eq!(back, instrument);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserializing_a_pair_without_a_crypto_side_fails() {
        let json = r#"{"type":"Crypto","base":{"name":"EUR","class":"Currency"},"price_quotation":{"name":"USD","class":"Currency"},"mic":"XXXX"}"#;
        let err = serde_json::from_str::<Instrument>(json).expect_err("no crypto side");
        assert_eq!(
            err.to_string(),
            "a crypto pair needs a crypto asset on one side: Currency|EUR/Currency|USD"
        );
    }

    #[cfg(feature = "serde")]
    #[test]
    fn crypto_is_owned() {
        _assert_owned::<Crypto>();
    }
}
