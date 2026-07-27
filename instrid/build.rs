use csv::ReaderBuilder;
use std::collections::HashMap;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

const CSV_PATH: &str = "./assets/ISO10383_MIC.csv";

/// MICs always compiled in. With `mic-full`, this filter is bypassed.
const CURATED: &[&[u8; 4]] = &[
    b"XNAS", b"XNYS", b"ARCX", b"BATS", b"IEXG", b"XASE", b"XCME", b"XCBT", b"XCBO", b"XNYM",
    b"XCEC", b"XLON", b"XPAR", b"XAMS", b"XBRU", b"XLIS", b"XETR", b"XFRA", b"XMIL", b"XSWX",
    b"XTKS", b"XHKG", b"XSHG", b"XSHE", b"XKRX", b"XASX", b"XBOM", b"XNSE", b"XTSE", b"XTSX",
    b"XEUR", b"XLBM", b"XSGE",
];

// Problem:
// --------
// Every time I try to implement some trait for Mic,
// my rust-analyzer freezes and raise memory usage.
//
// That was caused by the fact we had a giant match
// expression generated. Every time I change something,
// rust-analyzer would invalidate the whole generated file
// and start crunching it again.
//
// Due to the fact we are getting non-curated mics
// via getter function that has return type that
// naturally reminds HashMap::get's return type.
//
// I tried `phf` crate, lag was shorter, but present.
// Probably because of a lot of `::new(...)` inside phf values.
//
// Solution:
// ---------
// We want to initialize HashMap, it's natural,
// but we can't do it at comptime - RA dies.
//
// We will use OnceLock - a datastructure that
// may be uninitialized, but we can fill it at runtime.
//
// To carry data to runtime, we will embed data from
// ISO csv into `.bin` file as static bytes.
// But not all fields have comptime known size.
//
// We have such types in Mic:
// - known bytes at comptime ([u8; N])
// - Optional fields
//     - of known bytes at comptime
//     - unknown size bytes
// - enum variants
// - unknown size bytes (like market name)
//
// How to deal with unknown size bytes?
// We will try to use the same technique
// as std::ptr::slice_from_raw_parts(pointer, len).
//
// We will create 2 .bin(s).
//
// The second one will store sequence of bytes
// of all UNIQUE variable length strings.
// We need to know where each starts and its len
// in order to have:
//  - random access (we can read string @(offset, len) in O(1))
//  - due to random access, we can store only unique
//
// The first will carry all known size bytes and
// for unknown size bytes we will store:
// - 1 byte for Optional fields (0 means None)
// - 4 bytes to store offset in second file
// - 2 bytes to store len of variable length string.
//
// First    - `mic_records.bin`
// Second   - `mic_strings.bin`
//

// Per-record fixed-size binary layout.
// Keep in sync with the reader in mic.rs.
//
//   off  size  field
//   0    4     code [u8;4]
//   4    4     operating [u8;4]
//   8    1     mic_type (0=Operating, 1=Segment)
//   9    4     market_name_offset u32 LE
//   13   2     market_name_len    u16 LE
//   15   1     legal_entity_name_is_some
//   16   4     legal_entity_name_offset
//   20   2     legal_entity_name_len
//   22   1     lei_is_some
//   23   20    lei_bytes [u8;20]
//   43   1     category_tag (0..=14 known, 15 Unknown)
//   44   4     category_unknown_bytes [u8;4] (meaningful when tag==15)
//   48   1     acronym_is_some
//   49   4     acronym_offset
//   53   2     acronym_len
//   55   2     iso_country_code [u8;2]
//   57   4     city_offset
//   61   2     city_len
//   63   1     website_is_some
//   64   4     website_offset
//   68   2     website_len
//   70   1     status (0=Active, 1=Expired, 2=Updated, 3=Mock)
//   71   4     creation_date (year u16 LE, month u8, day u8)
//   75   4     last_update_date
//   79   1     last_validation_is_some
//   80   4     last_validation_date
//   84   1     expiry_is_some
//   85   4     expiry_date
//   89   1     comments_is_some
//   90   4     comments_offset
//   94   2     comments_len
//
//   total: 96 bytes
const RECORD_SIZE: usize = 96;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-changed={}", CSV_PATH);

    let full = env::var_os("CARGO_FEATURE_MIC_FULL").is_some();

    let mut reader = ReaderBuilder::new()
        .double_quote(true)
        .from_path(CSV_PATH)
        .expect("build.rs: failed to read ISO10383_MIC.csv");

    let mut records: Vec<u8> = Vec::new();
    let mut strings: Vec<u8> = Vec::new();
    let mut intern: HashMap<String, (u32, u16)> = HashMap::new();
    let mut ctors = String::new();
    let mut count = 0usize;

    for record in reader.records() {
        let row = record.expect("build.rs: malformed CSV row");

        let code = field(&row, 0);
        if code.len() != 4 {
            continue;
        }
        let code_bytes: [u8; 4] = code.as_bytes().try_into().unwrap();
        let is_curated = CURATED.iter().any(|c| **c == code_bytes);

        if !full && !is_curated {
            continue;
        }

        let start = records.len();
        write_record(&mut records, &mut strings, &mut intern, &row, &code_bytes);
        assert_eq!(
            records.len() - start,
            RECORD_SIZE,
            "record size mismatch for {code}",
        );

        if is_curated {
            let fn_name = code.to_ascii_lowercase();
            let market_name = field(&row, 3);
            let mic_type = field(&row, 2);
            let operating = field(&row, 1);
            let kind = match mic_type {
                "OPRT" => "operating".to_string(),
                "SGMT" => format!("segment of `{operating}`"),
                other => panic!("unknown MIC type: {other:?}"),
            };
            let expr = mic_expr(&row, &code_bytes);
            writeln!(
                ctors,
                "    /// {market_name} (`{code}`, {kind}).\n    pub const fn {fn_name}() -> Self {{ {expr} }}",
            )
            .unwrap();
        }

        count += 1;
    }

    let out_dir = env::var_os("OUT_DIR").expect("OUT_DIR not set");
    let out_dir = Path::new(&out_dir);
    fs::write(out_dir.join("mic_records.bin"), &records)
        .expect("build.rs: failed to write mic_records.bin");
    fs::write(out_dir.join("mic_strings.bin"), &strings)
        .expect("build.rs: failed to write mic_strings.bin");

    let body = format!(
        r#"// @generated by build.rs from {csv} ({count} entries, {bytes} record bytes, {strs} string bytes)

/// Curated MIC constructors. Always compiled in regardless of features.
impl MicIso {{
{ctors}}}
"#,
        csv = CSV_PATH,
        bytes = records.len(),
        strs = strings.len(),
    );
    fs::write(out_dir.join("mic_generated.rs"), body)
        .expect("build.rs: failed to write mic_generated.rs");
}

fn write_record(
    records: &mut Vec<u8>,
    strings: &mut Vec<u8>,
    intern: &mut HashMap<String, (u32, u16)>,
    row: &csv::StringRecord,
    code_bytes: &[u8; 4],
) {
    records.extend_from_slice(code_bytes); // code
    records.extend_from_slice(&parse_code4(field(row, 1))); // operating
    records.push(mic_type_byte(field(row, 2)));
    write_str(records, strings, intern, field(row, 3)); // market_name (required)
    write_opt_str(records, strings, intern, field(row, 4)); // legal_entity_name
    write_opt_lei(records, field(row, 5));
    write_category(records, field(row, 6));
    write_opt_str(records, strings, intern, field(row, 7)); // acronym
    records.extend_from_slice(&parse_code2(field(row, 8))); // iso_country_code
    write_str(records, strings, intern, field(row, 9)); // city (required)
    write_opt_str(records, strings, intern, field(row, 10)); // website
    records.push(status_byte(field(row, 11)));
    write_date(records, field(row, 12)).expect("missing creation_date");
    write_date(records, field(row, 13)).expect("missing last_update_date");
    write_opt_date(records, field(row, 14));
    write_opt_date(records, field(row, 15));
    write_opt_str(records, strings, intern, field(row, 16)); // comments
}

fn intern_str(
    strings: &mut Vec<u8>,
    intern: &mut HashMap<String, (u32, u16)>,
    s: &str,
) -> (u32, u16) {
    if let Some(v) = intern.get(s) {
        return *v;
    }
    let off = u32::try_from(strings.len()).expect("string pool overflow");
    let len = u16::try_from(s.len()).expect("string too long for u16");
    strings.extend_from_slice(s.as_bytes());
    intern.insert(s.to_owned(), (off, len));
    (off, len)
}

fn write_str(
    records: &mut Vec<u8>,
    strings: &mut Vec<u8>,
    intern: &mut HashMap<String, (u32, u16)>,
    s: &str,
) {
    let (off, len) = intern_str(strings, intern, s);
    records.extend_from_slice(&off.to_le_bytes());
    records.extend_from_slice(&len.to_le_bytes());
}

fn write_opt_str(
    records: &mut Vec<u8>,
    strings: &mut Vec<u8>,
    intern: &mut HashMap<String, (u32, u16)>,
    s: &str,
) {
    if s.is_empty() {
        records.push(0);
        records.extend_from_slice(&[0u8; 6]);
    } else {
        records.push(1);
        let (off, len) = intern_str(strings, intern, s);
        records.extend_from_slice(&off.to_le_bytes());
        records.extend_from_slice(&len.to_le_bytes());
    }
}

fn write_opt_lei(records: &mut Vec<u8>, s: &str) {
    if s.is_empty() {
        records.push(0);
        records.extend_from_slice(&[0u8; 20]);
    } else {
        assert_eq!(s.len(), 20, "expected 20-char LEI, got {s:?}");
        records.push(1);
        records.extend_from_slice(s.as_bytes());
    }
}

fn write_category(records: &mut Vec<u8>, s: &str) {
    let (tag, unknown): (u8, [u8; 4]) = match s {
        "APPA" => (0, [0; 4]),
        "ARMS" => (1, [0; 4]),
        "CASP" => (2, [0; 4]),
        "CTPS" => (3, [0; 4]),
        "DCMS" => (4, [0; 4]),
        "IDQS" => (5, [0; 4]),
        "MLTF" => (6, [0; 4]),
        "NSPD" => (7, [0; 4]),
        "OTFS" => (8, [0; 4]),
        "OTHR" => (9, [0; 4]),
        "RMKT" => (10, [0; 4]),
        "RMOS" => (11, [0; 4]),
        "SEFS" => (12, [0; 4]),
        "SINT" => (13, [0; 4]),
        "TRFS" => (14, [0; 4]),
        other if other.len() == 4 => (15, other.as_bytes().try_into().unwrap()),
        other => panic!("invalid market category code: {other:?}"),
    };
    records.push(tag);
    records.extend_from_slice(&unknown);
}

fn write_date(records: &mut Vec<u8>, s: &str) -> Option<()> {
    if s.is_empty() {
        return None;
    }
    let bytes = s.as_bytes();
    assert_eq!(bytes.len(), 8, "expected YYYYMMDD, got {s:?}");
    let year: u16 = s[0..4].parse().expect("invalid year");
    let month: u8 = s[4..6].parse().expect("invalid month");
    let day: u8 = s[6..8].parse().expect("invalid day");
    records.extend_from_slice(&year.to_le_bytes());
    records.push(month);
    records.push(day);
    Some(())
}

fn write_opt_date(records: &mut Vec<u8>, s: &str) {
    if s.is_empty() {
        records.push(0);
        records.extend_from_slice(&[0u8; 4]);
    } else {
        records.push(1);
        write_date(records, s).expect("non-empty date should write");
    }
}

fn mic_type_byte(s: &str) -> u8 {
    match s {
        "OPRT" => 0,
        "SGMT" => 1,
        other => panic!("unknown MIC type: {other:?}"),
    }
}

fn status_byte(s: &str) -> u8 {
    match s {
        "ACTIVE" => 0,
        "EXPIRED" => 1,
        "UPDATED" => 2,
        other => panic!("unknown MIC status: {other:?}"),
    }
}

fn parse_code4(s: &str) -> [u8; 4] {
    assert_eq!(s.len(), 4, "expected 4-char code, got {s:?}");
    s.as_bytes().try_into().unwrap()
}

fn parse_code2(s: &str) -> [u8; 2] {
    assert_eq!(s.len(), 2, "expected 2-char country code, got {s:?}");
    s.as_bytes().try_into().unwrap()
}

fn field(row: &csv::StringRecord, idx: usize) -> &str {
    row.get(idx).unwrap_or("").trim()
}

// --- Rust-source emission, used only for the curated `pub const fn` constructors. ---

fn mic_expr(row: &csv::StringRecord, code: &[u8; 4]) -> String {
    let code_str = std::str::from_utf8(code).unwrap();
    format!(
        "MicIso::new(AsciiCode::new(*b\"{code}\").unwrap(), AsciiCode::new({operating}).unwrap(), {market_name}, {mic_type}, \
         {legal_entity}, {lei}, {category}, {acronym}, AsciiCode::new({country}).unwrap(), {city}, \
         {website}, {status}, {creation}, {last_update}, {last_validation}, \
         {expiry}, {comments})",
        code = code_str,
        operating = code4_lit(field(row, 1)),
        mic_type = mic_type_lit(field(row, 2)),
        market_name = str_lit(field(row, 3)),
        legal_entity = opt_str_lit(field(row, 4)),
        lei = opt_lei_lit(field(row, 5)),
        category = category_lit(field(row, 6)),
        acronym = opt_str_lit(field(row, 7)),
        country = code2_lit(field(row, 8)),
        city = str_lit(field(row, 9)),
        website = opt_str_lit(field(row, 10)),
        status = status_lit(field(row, 11)),
        creation = date_lit(field(row, 12)).expect("missing creation date"),
        last_update = date_lit(field(row, 13)).expect("missing last_update date"),
        last_validation = opt_date_lit(field(row, 14)),
        expiry = opt_date_lit(field(row, 15)),
        comments = opt_str_lit(field(row, 16)),
    )
}

fn str_lit(s: &str) -> String {
    let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
    format!("\"{escaped}\"")
}

fn opt_str_lit(s: &str) -> String {
    if s.is_empty() {
        "None".into()
    } else {
        format!("Some({})", str_lit(s))
    }
}

fn code4_lit(s: &str) -> String {
    assert_eq!(s.len(), 4, "expected 4-char code, got {s:?}");
    format!("*b\"{s}\"")
}

fn code2_lit(s: &str) -> String {
    assert_eq!(s.len(), 2, "expected 2-char country code, got {s:?}");
    format!("*b\"{s}\"")
}

fn opt_lei_lit(s: &str) -> String {
    if s.is_empty() {
        return "None".into();
    }
    assert_eq!(s.len(), 20, "expected 20-char LEI, got {s:?}");
    format!("AsciiCode::new(*b\"{s}\")")
}

fn mic_type_lit(s: &str) -> &'static str {
    match s {
        "OPRT" => "MicType::Operating",
        "SGMT" => "MicType::Segment",
        other => panic!("unknown MIC type: {other:?}"),
    }
}

fn status_lit(s: &str) -> &'static str {
    match s {
        "ACTIVE" => "MicStatus::Active",
        "EXPIRED" => "MicStatus::Expired",
        "UPDATED" => "MicStatus::Updated",
        other => panic!("unknown MIC status: {other:?}"),
    }
}

fn category_lit(s: &str) -> String {
    let variant = match s {
        "APPA" => "Appa",
        "ARMS" => "Arms",
        "CASP" => "Casp",
        "CTPS" => "Ctps",
        "DCMS" => "Dcms",
        "IDQS" => "Idqs",
        "MLTF" => "Mltf",
        "NSPD" => "Nspd",
        "OTFS" => "Otfs",
        "OTHR" => "Othr",
        "RMKT" => "Rmkt",
        "RMOS" => "Rmos",
        "SEFS" => "Sefs",
        "SINT" => "Sint",
        "TRFS" => "Trfs",
        other if other.len() == 4 => {
            return format!("MarketCategoryCode::Unknown(*b\"{other}\")");
        }
        other => panic!("invalid market category code: {other:?}"),
    };
    format!("MarketCategoryCode::{variant}")
}

fn date_lit(s: &str) -> Option<String> {
    if s.is_empty() {
        return None;
    }
    let bytes = s.as_bytes();
    assert_eq!(bytes.len(), 8, "expected YYYYMMDD, got {s:?}");
    let year: u16 = s[0..4].parse().expect("invalid year");
    let month: u8 = s[4..6].parse().expect("invalid month");
    let day: u8 = s[6..8].parse().expect("invalid day");
    Some(format!("Date::new({year}, {month}, {day})"))
}

fn opt_date_lit(s: &str) -> String {
    match date_lit(s) {
        Some(d) => format!("Some({d})"),
        None => "None".into(),
    }
}
