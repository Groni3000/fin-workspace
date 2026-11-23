use super::*;

fn volume(s: &str) -> Volume {
    s.parse().expect("valid volume")
}

/// Test for decimals
#[test]
fn a_binance_volume_keeps_all_its_decimals() {
    let v = volume("278956.17487815");

    assert_eq!(v.value(), 278_956_174_878_150);
    assert_eq!(v.to_string(), "278956.17487815");
}

#[test]
fn whole_units_are_whole_numbers() {
    assert_eq!(Volume::from_units(308).value(), 308_000_000_000);
    assert_eq!(Volume::from_units(308), volume("308"));
    assert_eq!(Volume::from_units(308).to_string(), "308");
}

#[test]
fn a_fill_quantity_converts_without_loss() {
    let qty = Quantity::from_str_unchecked("1.000000001");

    assert_eq!(Volume::from(qty), volume("1.000000001"));
}

#[test]
#[should_panic(expected = "volume overflow")]
fn an_overflowing_sum_panics() {
    let _ = Volume::new(u128::MAX) + Volume::new(1);
}

#[test]
fn what_is_not_a_volume() {
    use ParseVolumeError::*;

    for (s, err) in [
        ("", InvalidFormat),
        (".5", InvalidFormat),
        ("5.", InvalidFormat),
        ("-1", InvalidFormat),
        ("+1", InvalidFormat),
        (" 1", InvalidFormat),
        ("1e3", InvalidFormat),
        ("1.2.3", InvalidFormat),
        ("0.0000000001", PrecisionError(10)),
        // 10^30 units: 10^39 raw, past `u128::MAX` (about 3.4·10^38).
        ("1000000000000000000000000000000", OutOfBounds),
    ] {
        assert_eq!(s.parse::<Volume>(), Err(err), "{s:?}");
    }
}
