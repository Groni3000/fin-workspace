use std::{error::Error, io::Error, str::FromStr};

/// Market Identifier Code (MIC) record as defined by ISO 10383.
///
/// Identifies a securities trading exchange, regulated market, or
/// other trading venue, along with descriptive metadata published
/// in the ISO MIC registry.
pub struct Mic {
    /// Four-character MIC assigned to the venue (e.g. `XNAS`).
    code: [u8; 4],
    /// MIC of the operating/parent venue. Equals `code` for operating MICs.
    operating: [u8; 4],
    /// Whether this entry is an operating MIC or a market segment MIC.
    mic_type: MicType,
    /// Full registered name of the market or venue.
    market_name: String,
    /// Legal entity that operates the venue.
    legal_entity_name: Option<String>,
    /// 20-character ISO 17442 Legal Entity Identifier of the operator.
    lei_code: Option<[u8; 20]>,
    /// Category of market (e.g. regulated market, MTF, OTF, SI).
    market_category_code: MarketCategoryCode,
    /// Common acronym for the venue, if any.
    acronym: Option<String>,
    /// ISO 3166-1 alpha-2 country code of the venue's jurisdiction.
    iso_country_code: [u8; 2],
    /// City where the venue is located.
    city: String,
    /// Public website URL of the venue.
    website: Option<String>,
    /// Current registry status of the MIC.
    status: MicStatus,
    /// Date the MIC was created, as `YYYYMMDD`.
    creation_date: [u8; 8],
    /// Date of the most recent update to the record, as `YYYYMMDD`.
    last_update_date: [u8; 8],
    /// Date the record was last validated by the registrar, as `YYYYMMDD`.
    last_validation_date: Option<[char; 8]>,
    /// Date the MIC expired or will expire, as `YYYYMMDD`.
    expiry_date: Option<[u8; 8]>,
    /// Free-form notes published with the registry entry.
    comments: Option<String>,
}

/// Distinguishes top-level operating MICs from their market segments.
enum MicType {
    /// Operating MIC: identifies the venue itself.
    Operating,
    /// Segment MIC: identifies a specific market segment within an operating MIC.
    Segment,
}

/// Lifecycle status of a MIC entry in the ISO registry.
enum MicStatus {
    /// Currently in use.
    Active,
    /// No longer in use; retained for historical reference.
    Expired,
    /// At least one field is changed in the current monthly publication.
    Updated,
}

/// ISO 10383 market category code — classifies the regulatory or functional
/// type of a trading venue.
///
/// The `Unknown` variant carries any 4-character code not recognised by this
/// enum, so registry entries with newly-introduced categories can still be
/// represented round-trip.
enum MarketCategoryCode {
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
    Unknown([char; 4]),
}

/// Calendar date as published by ISO 10383 registry (`YYYYMMDD`)
///
/// No timezone, no validation beyond field ranges.
/// Ordered chronologically via the derived Ord.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct Date {
    year: u16,
    month: u8,
    day: u8,
}

impl Date {
    pub const fn new(year: u16, month: u8, day: u8) -> Self {
        Self { year, month, day }
    }
}

pub enum DateParseError {
    InvalidLenght,
    NotDigits,
}

impl FromStr for Date {
    type Err = DateParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let bytes = s.as_bytes();

        if bytes.len() != 8 {
            return Err(DateParseError::InvalidLenght);
        };
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
