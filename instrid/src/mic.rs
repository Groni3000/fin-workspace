use std::{fmt::Display, str::FromStr};

/// Market Identifier Code (MIC) record as defined by ISO 10383.
///
/// Identifies a securities trading exchange, regulated market, or
/// other trading venue, along with descriptive metadata published
/// in the ISO MIC registry.
#[derive(Debug, PartialEq, Eq, Default)]
pub struct Mic {
    /// Four-character MIC assigned to the venue (e.g. `XNAS`).
    code: [u8; 4],
    /// MIC of the operating/parent venue. Equals `code` for operating MICs.
    operating: [u8; 4],
    /// Whether this entry is an operating MIC or a market segment MIC.
    mic_type: MicType,
    /// Full registered name of the market or venue.
    market_name: &'static str,
    /// Legal entity that operates the venue.
    legal_entity_name: Option<&'static str>,
    /// 20-character ISO 17442 Legal Entity Identifier of the operator.
    lei_code: Option<[u8; 20]>,
    /// Category of market (e.g. regulated market, MTF, OTF, SI).
    market_category_code: MarketCategoryCode,
    /// Common acronym for the venue, if any.
    acronym: Option<&'static str>,
    /// ISO 3166-1 alpha-2 country code of the venue's jurisdiction.
    iso_country_code: [u8; 2],
    /// City where the venue is located.
    city: &'static str,
    /// Public website URL of the venue.
    website: Option<&'static str>,
    /// Current registry status of the MIC.
    status: MicStatus,
    /// Date the MIC was created, as `YYYYMMDD`.
    creation_date: Date,
    /// Date of the most recent update to the record, as `YYYYMMDD`.
    last_update_date: Date,
    /// Date the record was last validated by the registrar, as `YYYYMMDD`.
    last_validation_date: Option<Date>,
    /// Date the MIC expired or will expire, as `YYYYMMDD`.
    expiry_date: Option<Date>,
    /// Free-form notes published with the registry entry.
    comments: Option<&'static str>,
}

impl Mic {
    pub const fn new(
        code: [u8; 4],
        operating: [u8; 4],
        market_name: &'static str,
        mic_type: MicType,
        legal_entity_name: Option<&'static str>,
        lei_code: Option<[u8; 20]>,
        market_category_code: MarketCategoryCode,
        acronym: Option<&'static str>,
        iso_country_code: [u8; 2],
        city: &'static str,
        website: Option<&'static str>,
        status: MicStatus,
        creation_date: Date,
        last_update_date: Date,
        last_validation_date: Option<Date>,
        expiry_date: Option<Date>,
        comments: Option<&'static str>,
    ) -> Self {
        Mic {
            code,
            operating,
            mic_type,
            market_name,
            legal_entity_name,
            lei_code,
            market_category_code,
            acronym,
            iso_country_code,
            city,
            website,
            status,
            creation_date,
            last_update_date,
            last_validation_date,
            expiry_date,
            comments,
        }
    }
}

impl Display for Mic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            std::str::from_utf8(&self.code).expect("MIC must be a valid ASCII")
        )
    }
}

/// Distinguishes top-level operating MICs from their market segments.
#[derive(Debug, PartialEq, Eq)]
pub enum MicType {
    /// Operating MIC: identifies the venue itself.
    Operating,
    /// Segment MIC: identifies a specific market segment within an operating MIC.
    Segment,
}

impl Default for MicType {
    fn default() -> Self {
        MicType::Operating
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnknownMicType;

impl FromStr for MicType {
    type Err = UnknownMicType;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "OPRT" => Ok(MicType::Operating),
            "SGMT" => Ok(MicType::Segment),
            _ => Err(UnknownMicType),
        }
    }
}

/// Lifecycle status of a MIC entry in the ISO registry.
#[derive(Debug, PartialEq, Eq)]
pub enum MicStatus {
    /// Currently in use.
    Active,
    /// No longer in use; retained for historical reference.
    Expired,
    /// At least one field is changed in the current monthly publication.
    Updated,
    /// Used for internal testing
    Mock,
}

impl Default for MicStatus {
    fn default() -> Self {
        MicStatus::Mock
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnknownMicStatus;

impl FromStr for MicStatus {
    type Err = UnknownMicStatus;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "ACTIVE" => Ok(MicStatus::Active),
            "EXPIRED" => Ok(MicStatus::Expired),
            "UPDATED" => Ok(MicStatus::Updated),
            _ => Err(UnknownMicStatus),
        }
    }
}

/// ISO 10383 market category code — classifies the regulatory or functional
/// type of a trading venue.
///
/// The `Unknown` variant carries any 4-character code not recognised by this
/// enum, so registry entries with newly-introduced categories can still be
/// represented round-trip.
#[derive(Debug, PartialEq, Eq)]
pub enum MarketCategoryCode {
    /// `APPA` — Approved Publication Arrangement (MiFID II trade publication).
    Appa,
    /// `ARMS` — Approved Reporting Mechanism (MiFID II transaction reporting).
    Arms,
    /// `CASP` — Crypto-Asset Service Provider.
    Casp,
    /// `CTPS` — Consolidated Tape Provider.
    Ctps,
    /// `DCMS` — Designated Contract Market.
    Dcms,
    /// `IDQS` — Interdealer Quotation System.
    Idqs,
    /// `MLTF` — Multilateral Trading Facility (MTF).
    Mltf,
    /// `NSPD` — Not Specified / unclassified.
    Nspd,
    /// `OTFS` — Organised Trading Facility (OTF).
    Otfs,
    /// `OTHR` — Other.
    Othr,
    /// `RMKT` — Regulated Market.
    Rmkt,
    /// `RMOS` — Recognised Market Operator.
    Rmos,
    /// `SEFS` — Swap Execution Facility.
    Sefs,
    /// `SINT` — Systematic Internaliser.
    Sint,
    /// `TRFS` — Trade Reporting Facility.
    Trfs,
    /// Any 4-character code not covered by the variants above.
    Unknown([u8; 4]),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MktCatCodeParseError {
    InvalidLength,
}

impl FromStr for MarketCategoryCode {
    type Err = MktCatCodeParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != 4 {
            return Err(MktCatCodeParseError::InvalidLength);
        }
        let bytes = s.as_bytes();
        let arr: [u8; 4] = [bytes[0], bytes[1], bytes[2], bytes[3]];

        Ok(match &arr {
            b"APPA" => MarketCategoryCode::Appa,
            b"ARMS" => MarketCategoryCode::Arms,
            b"CASP" => MarketCategoryCode::Casp,
            b"CTPS" => MarketCategoryCode::Ctps,
            b"DCMS" => MarketCategoryCode::Dcms,
            b"IDQS" => MarketCategoryCode::Idqs,
            b"MLTF" => MarketCategoryCode::Mltf,
            b"NSPD" => MarketCategoryCode::Nspd,
            b"OTFS" => MarketCategoryCode::Otfs,
            b"OTHR" => MarketCategoryCode::Othr,
            b"RMKT" => MarketCategoryCode::Rmkt,
            b"RMOS" => MarketCategoryCode::Rmos,
            b"SEFS" => MarketCategoryCode::Sefs,
            b"SINT" => MarketCategoryCode::Sint,
            b"TRFS" => MarketCategoryCode::Trfs,
            _ => MarketCategoryCode::Unknown(arr),
        })
    }
}

impl Default for MarketCategoryCode {
    fn default() -> Self {
        MarketCategoryCode::Unknown([0; 4])
    }
}

/// Calendar date as published by ISO 10383 registry (`YYYYMMDD`)
///
/// No timezone, no validation beyond field ranges.
/// Ordered chronologically via the derived Ord.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Date {
    year: u16,
    month: u8,
    day: u8,
}

impl Default for Date {
    fn default() -> Self {
        Self {
            year: 1970,
            month: 1,
            day: 1,
        }
    }
}

impl Date {
    pub const fn new(year: u16, month: u8, day: u8) -> Self {
        Self { year, month, day }
    }
}

#[derive(Debug)]
pub enum DateParseError {
    InvalidLength,
    NotDigits,
}

impl FromStr for Date {
    type Err = DateParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let bytes = s.as_bytes();

        if bytes.len() != 8 {
            return Err(DateParseError::InvalidLength);
        }
        if !bytes.iter().all(|b| b.is_ascii_digit()) {
            return Err(DateParseError::NotDigits);
        }

        let year = parse4(&bytes[0..4]);
        let month = parse2(&bytes[4..6]);
        let day = parse2(&bytes[6..8]);

        Ok(Date::new(year, month, day))
    }
}

fn parse2(bytes: &[u8]) -> u8 {
    (bytes[0] - b'0') * 10 + (bytes[1] - b'0')
}

fn parse4(bytes: &[u8]) -> u16 {
    (bytes[0] - b'0') as u16 * 1000
        + (bytes[1] - b'0') as u16 * 100
        + (bytes[2] - b'0') as u16 * 10
        + (bytes[3] - b'0') as u16
}

impl Display for Date {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:04}{:02}{:02}", self.year, self.month, self.day)
    }
}

/// Hand-written constructors for commonly used MICs.
///
/// Until `build.rs` codegen from `assets/ISO10383_MIC.csv` lands, add entries
/// here as needed.
impl Mic {
    /// NASDAQ - ALL MARKETS (operating MIC).
    pub const fn xnas() -> Self {
        Mic::new(
            *b"XNAS",
            *b"XNAS",
            "NASDAQ - ALL MARKETS",
            MicType::Operating,
            Some("NASDAQ, INC."),
            Some(*b"549300L8X1Q78ERXFD06"),
            MarketCategoryCode::Rmkt,
            Some("NASDAQ"),
            *b"US",
            "NEW YORK",
            Some("WWW.NASDAQ.COM"),
            MicStatus::Updated,
            Date::new(2005, 6, 27),
            Date::new(2026, 4, 27),
            Some(Date::new(2026, 4, 27)),
            None,
            None,
        )
    }
}
