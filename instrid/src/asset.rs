/// Represents an asset (e.g., equity, commodity, currency, etc.).
///
/// Asset - an entity that can be traded or cash settled.
///
/// Examples:
///     - AAPL, Equity
///     - USD, Currency
///     - BTC, Currency
///     - S&P 500, Index (cash settled)
#[derive(Debug, PartialEq, Eq)]
pub struct Asset {
    name: &'static str,
    category: AssetClass,
}

impl Asset {
    pub const fn new(name: &'static str, category: AssetClass) -> Self {
        Self { name, category }
    }
}

/// Represents the class or type of an asset (e.g., equity, commodity, currency, etc.).
#[derive(Debug, PartialEq, Eq)]
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_asset_new() {
        let name = "AAPL";
        let asset_class = AssetClass::Equity;
        let aapl = Asset::new(name, asset_class);
        dbg!(&aapl);
        assert_eq!(&aapl.name, &name);
        assert_eq!(&aapl.category, &AssetClass::Equity);
    }
}
