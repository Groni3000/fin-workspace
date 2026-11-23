use super::*;
use ParseDecimalError::*;

fn raw(s: &str) -> Result<i128, ParseDecimalError> {
    parse_decimal(s, 9)?.signed()
}

#[test]
fn digits_with_at_most_one_dot_and_an_optional_minus() {
    for (s, want) in [
        ("0", 0),
        ("308", 308_000_000_000),
        ("1.5", 1_500_000_000),
        ("007.10", 7_100_000_000),
        ("0.000000001", 1),
        ("-1.5", -1_500_000_000),
        ("-0", 0),
    ] {
        assert_eq!(raw(s), Ok(want), "{s:?}");
    }
}

/// Before this parser, `1.+5` parsed as 1.05, `1 . 5` as 1.5, and `+1` and padded strings
/// as numbers.
#[test]
fn nothing_else_is_a_decimal() {
    for s in [
        "",
        "-",
        ".5",
        "5.",
        "-.5",
        "+1",
        "1.+5",
        "0.-5",
        "--1",
        " 1",
        "1 ",
        "1 . 5",
        "1e3",
        "1.2.3",
        "1,5",
        // A non-digit in a part too long for `u64`.
        "12345678901234567890x",
    ] {
        assert_eq!(raw(s), Err(InvalidFormat), "{s:?}");
    }
}

#[test]
fn a_minus_is_refused_where_a_type_cant_be_negative() {
    assert_eq!(parse_decimal("1", 9).unwrap().unsigned(), Ok(1_000_000_000));
    assert_eq!(
        parse_decimal("-1", 9).unwrap().unsigned(),
        Err(InvalidFormat)
    );
    assert_eq!(
        parse_decimal("-0", 9).unwrap().unsigned(),
        Err(InvalidFormat)
    );
}

#[test]
fn the_fraction_is_scaled_to_the_precision() {
    assert_eq!(parse_decimal("1.5", 2).unwrap().unsigned(), Ok(150));
    assert_eq!(parse_decimal("1.25", 2).unwrap().unsigned(), Ok(125));
    assert_eq!(parse_decimal("1.255", 2), Err(PrecisionError(3)));
}

#[test]
fn what_doesnt_fit_is_out_of_bounds() {
    // Too many digits for `u128` before any scaling.
    assert_eq!(parse_decimal(&"9".repeat(40), 0), Err(OutOfBounds));
    // 10^39 raw, past `u128::MAX`.
    assert_eq!(
        parse_decimal("1000000000000000000000000000000", 9),
        Err(OutOfBounds)
    );
    // 2·10^38 raw fits `u128` but not `i128`.
    let past_i128 = parse_decimal("200000000000000000000000000000", 9).unwrap();
    assert_eq!(past_i128.signed(), Err(OutOfBounds));
}

/// Most values are parsed in `u64`; these must fall back to `u128`.
#[test]
fn values_past_u64_are_parsed_in_u128() {
    // 20 digits, past `u64::MAX`.
    assert_eq!(
        parse_decimal("99999999999999999999", 0).unwrap().unsigned(),
        Ok(99_999_999_999_999_999_999)
    );
    // The whole part fits `u64`, the raw value (10^22) doesn't.
    assert_eq!(
        parse_decimal("10000000000000.5", 9).unwrap().unsigned(),
        Ok(10_000_000_000_000_500_000_000)
    );
}
