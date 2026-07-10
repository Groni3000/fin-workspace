#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "serde")]
use std::borrow::Cow;
use std::cmp::Eq;
use std::{fmt::Display, str::FromStr};

/// Market Identifier Code (MIC) record as defined by ISO 10383.
///
/// Identifies a securities trading exchange, regulated market, or
/// other trading venue, along with descriptive metadata published
/// in the ISO MIC registry.
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, Default)]
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

impl PartialEq for Mic {
    fn eq(&self, other: &Self) -> bool {
        self.code == other.code
    }
}

impl Eq for Mic {}

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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[cfg(feature = "serde")]
impl Serialize for Mic {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(
            std::str::from_utf8(self.code.as_slice())
                .map_err(|_err| serde::ser::Error::custom("Code should be a valid UTF-8"))?,
        )
    }
}

#[cfg(feature = "serde")]
impl<'de> Deserialize<'de> for Mic {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s: Cow<'de, str> = Deserialize::deserialize(deserializer)?;
        mic_by_code(&s).ok_or_else(|| serde::de::Error::custom(format!("MIC not found: {s}")))
    }
}

include!(concat!(env!("OUT_DIR"), "/mic_generated.rs"));

// --- MIC registry: embedded binary blob, parsed once on first lookup. ---
//
// The full registry is not emitted as Rust source: a single expression
// containing thousands of `Mic::new(...)` calls is very slow for
// rust-analyzer to type-check on every edit that touches `Mic`. Instead
// we ship two `&'static [u8]` blobs and build a `HashMap<[u8;4], Mic>`
// lazily on first call.
//
// `&'static str` fields of `Mic` are reconstructed as slices of the
// `MIC_STRINGS` blob — slicing a `'static` byte slice yields a `'static`
// string slice, so no allocation or leaking is required.

use std::collections::HashMap;
use std::sync::OnceLock;

static MIC_RECORDS: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/mic_records.bin"));
static MIC_STRINGS: &[u8] = include_bytes!(concat!(env!("OUT_DIR"), "/mic_strings.bin"));

// Keep in sync with the layout documented in build.rs.
const RECORD_SIZE: usize = 96;

static REGISTRY: OnceLock<HashMap<[u8; 4], Mic>> = OnceLock::new();

fn registry() -> &'static HashMap<[u8; 4], Mic> {
    REGISTRY.get_or_init(|| {
        debug_assert_eq!(
            MIC_RECORDS.len() % RECORD_SIZE,
            0,
            "MIC_RECORDS not a multiple of RECORD_SIZE",
        );
        let n = MIC_RECORDS.len() / RECORD_SIZE;
        let mut map = HashMap::with_capacity(n);
        for i in 0..n {
            let rec = &MIC_RECORDS[i * RECORD_SIZE..(i + 1) * RECORD_SIZE];
            let mic = parse_record(rec);
            map.insert(mic.code, mic);
        }
        map
    })
}

/// Returns the registry record for a MIC code, if known to this build.
///
/// By default only common MICs are compiled in (~30 entries).
/// Enable the `mic-full` feature for the full ISO 10383 registry.
///
/// Returns `None` for any code that isn't an exact 4-character match
/// against a known MIC.
///
/// # Examples
///
/// ```
/// use instrid::mic::mic_by_code;
///
/// assert!(mic_by_code("XNAS").is_some());
/// assert!(mic_by_code("ZZZZ").is_none());
/// assert!(mic_by_code("XNA").is_none());   // wrong length
/// ```
pub fn mic_by_code(code: &str) -> Option<Mic> {
    let bytes: &[u8; 4] = code.as_bytes().try_into().ok()?;
    registry().get(bytes).copied()
}

fn parse_record(r: &[u8]) -> Mic {
    let code: [u8; 4] = r[0..4].try_into().unwrap();
    let operating: [u8; 4] = r[4..8].try_into().unwrap();
    let mic_type = match r[8] {
        0 => MicType::Operating,
        1 => MicType::Segment,
        b => panic!("invalid mic_type byte: {b}"),
    };
    let market_name = read_str(&r[9..15]);
    let legal_entity_name = read_opt_str(&r[15..22]);
    let lei_code = read_opt_lei(&r[22..43]);
    let market_category_code = read_category(&r[43..48]);
    let acronym = read_opt_str(&r[48..55]);
    let iso_country_code: [u8; 2] = r[55..57].try_into().unwrap();
    let city = read_str(&r[57..63]);
    let website = read_opt_str(&r[63..70]);
    let status = match r[70] {
        0 => MicStatus::Active,
        1 => MicStatus::Expired,
        2 => MicStatus::Updated,
        3 => MicStatus::Mock,
        b => panic!("invalid status byte: {b}"),
    };
    let creation_date = read_date(&r[71..75]);
    let last_update_date = read_date(&r[75..79]);
    let last_validation_date = read_opt_date(&r[79..84]);
    let expiry_date = read_opt_date(&r[84..89]);
    let comments = read_opt_str(&r[89..96]);

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

fn read_str(field: &[u8]) -> &'static str {
    // 4 bytes offset + 2 bytes len
    let off = u32::from_le_bytes(field[0..4].try_into().unwrap()) as usize;
    let len = u16::from_le_bytes(field[4..6].try_into().unwrap()) as usize;
    std::str::from_utf8(&MIC_STRINGS[off..off + len]).expect("invalid UTF-8 in MIC string pool")
}

fn read_opt_str(field: &[u8]) -> Option<&'static str> {
    if field[0] == 0 {
        return None;
    }
    Some(read_str(&field[1..7]))
}

fn read_opt_lei(field: &[u8]) -> Option<[u8; 20]> {
    if field[0] == 0 {
        return None;
    }
    Some(field[1..21].try_into().unwrap())
}

fn read_category(field: &[u8]) -> MarketCategoryCode {
    let unknown: [u8; 4] = field[1..5].try_into().unwrap();
    match field[0] {
        0 => MarketCategoryCode::Appa,
        1 => MarketCategoryCode::Arms,
        2 => MarketCategoryCode::Casp,
        3 => MarketCategoryCode::Ctps,
        4 => MarketCategoryCode::Dcms,
        5 => MarketCategoryCode::Idqs,
        6 => MarketCategoryCode::Mltf,
        7 => MarketCategoryCode::Nspd,
        8 => MarketCategoryCode::Otfs,
        9 => MarketCategoryCode::Othr,
        10 => MarketCategoryCode::Rmkt,
        11 => MarketCategoryCode::Rmos,
        12 => MarketCategoryCode::Sefs,
        13 => MarketCategoryCode::Sint,
        14 => MarketCategoryCode::Trfs,
        15 => MarketCategoryCode::Unknown(unknown),
        b => panic!("invalid category tag: {b}"),
    }
}

fn read_date(field: &[u8]) -> Date {
    let year = u16::from_le_bytes(field[0..2].try_into().unwrap());
    let month = field[2];
    let day = field[3];
    Date::new(year, month, day)
}

fn read_opt_date(field: &[u8]) -> Option<Date> {
    if field[0] == 0 {
        return None;
    }
    Some(read_date(&field[1..5]))
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "serde")]
    use serde_json::json;

    use super::*;
    #[cfg(feature = "serde")]
    use crate::_assert_owned;

    #[test]
    fn xnas_lookup_returns_some() {
        assert!(mic_by_code("XNAS").is_some());
    }

    #[test]
    fn unknown_code_returns_none() {
        assert!(mic_by_code("ZZZZ").is_none());
    }

    #[test]
    fn wrong_length_returns_none() {
        assert!(mic_by_code("XNA").is_none());
        assert!(mic_by_code("XNASD").is_none());
        assert!(mic_by_code("").is_none());
    }

    /// Hits `visit_borrowed_str(&'de str)`
    #[cfg(feature = "mic-full")]
    #[test]
    fn full_registry_includes_obscure_mic() {
        // Present only in the full registry, not in the curated set.
        assert!(mic_by_code("DRSP").is_some());
    }

    /// Hits `visit_str(&str)`
    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_mic_from_reader() {
        // from_reader can NEVER borrow from `'de` (bytes live in a read buffer),
        let json = "\"XCEC\"";
        let reader = std::io::Cursor::new(json.as_bytes().to_vec());
        let mic: Mic = serde_json::from_reader(reader).expect("from_reader should work");
        assert_eq!(mic, Mic::xcec());
    }

    /// Hits `visit_string(String)`
    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_mic_from_value() {
        let val = json!("XCEC");
        let mic: Mic = serde_json::from_value(val).expect("from_value should work");
        assert_eq!(mic, Mic::xcec());
    }

    /// Hits `visit_borrowed_str(&'de str)`
    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_mic_from_value_ref() {
        let input = "XCEC".to_string();
        let val = json!(&input);
        let mic: Mic = serde_json::from_value(val).expect("from_value should work");
        assert_eq!(mic, Mic::xcec());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serialize_curated_mic() {
        let mic = Mic::xcec();
        let serialized = serde_json::to_string(&mic).expect("Mic should be serializable");
        let expected = "\"XCEC\"";

        assert_eq!(serialized, expected);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn deserialize_curated_mic() {
        let str_mic = "\"XCEC\"";
        let mic: Mic = serde_json::from_str(str_mic).expect("Mic should be deserializable");
        let expected = Mic::xcec();

        assert_eq!(mic, expected);
    }

    #[cfg(all(feature = "mic-full", feature = "serde"))]
    #[test]
    fn serialize_full_registry_mic() {
        // Present only in the full registry, not in the curated set.
        let mic = mic_by_code("DRSP").expect("Mic not found");
        let serialized = serde_json::to_string(&mic).expect("Mic should be serializable");
        let expected = "\"DRSP\"";

        assert_eq!(serialized, expected);
    }

    #[cfg(all(feature = "mic-full", feature = "serde"))]
    #[test]
    fn deserialize_full_registry_mic() {
        let mic_str = "\"DRSP\"";
        let mic: Mic = serde_json::from_str(&mic_str).expect("Mic should be deserializable");
        let expected = mic_by_code("DRSP").expect("Mic not found");

        assert_eq!(mic, expected);
    }

    /// Mic should not borrow from a deserializer input
    #[cfg(feature = "serde")]
    #[test]
    fn test_mic_is_owned() {
        _assert_owned::<Mic>();
    }
}
