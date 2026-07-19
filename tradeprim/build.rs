use std::collections::{HashMap, HashSet};
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

// https://www.iso.org/iso-4217-currency-codes.html
// https://datahub.io/core/currency-codes
// `ISO 4217` - Currency
// Schema
//
// Field	        | Type	    | Description	                                                                                                                                 | Title
// Entity	        | string	| Country or region name
// Currency	        | string	| Name of the currency
// AlphabeticCode	| string	| 3 digit alphabetic code for the currency	                                                                                                     | Alphabetic Code
// NumericCode	    | string	| 3 digit numeric code (zero-padded, e.g. '008')	                                                                                             | Numeric Code
// MinorUnit	    | string	| Number of digits after the decimal separator; '-' for currencies with no minor unit defined                                                    | Minor Unit
// WithdrawalDate	| string	| Date the currency was withdrawn; values may be a year-month (YYYY-MM) or a date range (e.g. '1990-07 to 1990-09'); empty for current currencies| Withdrawal Date
//
// WithdrawalDate is Optional
//
// So, the record schema for a valid currency is:
// off  size    field
// 0    4       entity offset u32
// 4    2       entity length u16
// 6    4       currency name offset u32
// 10   2       currency name length u16
// 12   3       3-digit alphabetic code [u8; 3]
// 15   3       3-digit numeric code [u8; 3]
// 18   1       major unit precision (number of digits after the decimal separator), if `-` => precision 0, if `` => withdrawal date
//
// TOTAL: 19 bytes / record
const ISO_4217_CSV_PATH: &str = "./assets/Currency-ISO-4217.csv";
/// Currencies that are compiled in.
const CURATED: &[&[u8; 3]] = &[b"USD", b"EUR", b"GBP", b"JPY", b"CHF"];
const CURRENCY_RECORD_SIZE: usize = 19;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!("cargo::rerun-if-changed={}", ISO_4217_CSV_PATH);
    let out_dir = &env::var("OUT_DIR").unwrap();
    let out_dir = Path::new(out_dir);
    let mut reader = csv::ReaderBuilder::new()
        .double_quote(true)
        .from_path("assets/Currency-ISO-4217.csv")
        .expect("build.rs: failed to read Currencies csv");

    let mut records: Vec<u8> = Vec::new();
    let mut strings: Vec<u8> = Vec::new();
    let mut off_len_map: HashMap<String, (u32, u16)> = HashMap::new();
    let mut expressions = String::new();
    // We will ignore all seen currencies.
    let mut seen_currencies: HashSet<[u8; 3]> = HashSet::new();

    for record in reader.records() {
        let row = record.expect("build.rs: malformed CSV row");
        assert_eq!(row.len(), 6);
        // First of all - skip row if currency is withdrawn.
        if !row.get(5).unwrap().trim().is_empty() {
            continue;
        }
        // Get all values
        let Some(entity) = row.get(0).map(|x| x.trim()) else {
            continue;
        };
        let Some(currency_name) = row.get(1).map(|x| x.trim()) else {
            continue;
        };
        let Some(alphabetic_code) = row.get(2).map(|x| x.trim()) else {
            continue;
        };
        if alphabetic_code.len() != 3 {
            continue;
        }
        let Some(numeric_code) = row.get(3).map(|x| x.trim()) else {
            continue;
        };
        if numeric_code.len() != 3 {
            continue;
        }
        // Values with `-` means no minor unit defined => 0
        let Some(major_unit_precision) = row.get(4).map(|x| {
            let trimmed = x.trim();
            if trimmed.eq("-") || trimmed.is_empty() {
                return 0;
            } else {
                return trimmed
                    .parse::<u8>()
                    .expect("major_unit_precision must be a valid u8");
            }
        }) else {
            continue;
        };

        // One record per currency code.
        let code_bytes: &[u8; 3] = alphabetic_code.as_bytes().try_into().unwrap();
        if !seen_currencies.insert(*code_bytes) {
            continue;
        }

        let init_len = records.len();
        // Write various length fields
        if !off_len_map.contains_key(entity) {
            off_len_map.insert(
                entity.to_string(),
                (strings.len() as u32, entity.len() as u16),
            );
            strings.extend_from_slice(entity.as_bytes());
        }
        records.extend_from_slice(&(off_len_map.get(entity).unwrap().0).to_le_bytes());
        records.extend_from_slice(&(off_len_map.get(entity).unwrap().1).to_le_bytes());

        if !off_len_map.contains_key(currency_name) {
            off_len_map.insert(
                currency_name.to_string(),
                (strings.len() as u32, currency_name.len() as u16),
            );
            strings.extend_from_slice(currency_name.as_bytes());
        }
        records.extend_from_slice(&(off_len_map.get(currency_name).unwrap().0).to_le_bytes());
        records.extend_from_slice(&(off_len_map.get(currency_name).unwrap().1).to_le_bytes());

        // Write comptime known length fields
        records
            .extend_from_slice(TryInto::<&[u8; 3]>::try_into(alphabetic_code.as_bytes()).unwrap());
        records.extend_from_slice(TryInto::<&[u8; 3]>::try_into(numeric_code.as_bytes()).unwrap());
        records.push(TryInto::<u8>::try_into(major_unit_precision).unwrap());

        assert_eq!(CURRENCY_RECORD_SIZE, records.len() - init_len);

        // Emit a `pub const fn` constructor for each curated currency,
        // just like the `mic_expr` in instrid/build.rs.
        if CURATED.contains(&code_bytes) {
            let fn_name = alphabetic_code.to_ascii_lowercase();
            writeln!(
                expressions,
                "    /// {name} (`{code}`, ISO 4217 numeric {numeric}, {precision} minor digits).\n    \
                 pub const fn {fn_name}() -> Self {{ \
                 Currency::new({name_lit}, {code_lit}, {numeric_lit}, {precision}) }}",
                name = currency_name,
                code = alphabetic_code,
                numeric = numeric_code,
                name_lit = str_literal(currency_name),
                code_lit = str_literal(alphabetic_code),
                numeric_lit = str_literal(numeric_code),
                precision = major_unit_precision,
            )
            .expect("build.rs: failed to write currency ctor");
        }
    }

    println!(
        "cargo::warning=records={} strings={}",
        records.len() / 19,
        strings.len()
    );
    fs::write(out_dir.join("currency_strings.bin"), strings)
        .expect("failed to write currency_strings.bin");
    fs::write(out_dir.join("currency_records.bin"), records)
        .expect("failed to write currency_records.bin");

    let generated = format!(
        "// @generated by build.rs from {}\n\n\
         /// Curated ISO 4217 currency constructors. Always compiled in.\n\
         impl Currency {{\n{}}}\n",
        ISO_4217_CSV_PATH, expressions
    );
    fs::write(out_dir.join("currency_generated.rs"), generated)
        .expect("failed to write currency_generated.rs");
}

/// Renders a `&str` as an escaped Rust string literal (`"..."`).
fn str_literal(s: &str) -> String {
    let escaped = s.replace('\\', "\\\\").replace('"', "\\\"");
    format!("\"{escaped}\"")
}
