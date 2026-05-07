#[derive(Debug)]
pub struct Asset {
    bytes: [u8; 8],
    len: u8,
    category: AssetClass,
}

#[derive(Debug)]
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
