use std::{fmt::Display, num::ParseIntError, str::FromStr};

use tradeprim::{
    currency::Currency,
    currency_notional::CurrencyNotional,
    price::Price,
    quantity::{QtyStep, Quantity},
    quote_notional::QuoteNotional,
};

/// Has essential trading specification parameters.
///
pub trait Spec {
    fn tick_size_price(&self) -> Price;
    fn tick_size_currency(&self) -> (Price, Currency);
    fn point_value(&self) -> PointValue;
    fn currency_notional(&self, quote_notional: QuoteNotional) -> CurrencyNotional;
    fn min_quantity(&self) -> Quantity;
    fn step_qty(&self) -> QtyStep;

    // --- Validation

    /// Returns `true` if, **roughly speaking**, `price.is_multiple_of(tick)`.
    ///
    /// Price does not require rounding to plug in orders.
    fn is_price_on_tick(&self, price: Price) -> bool {
        price
            .value()
            .unsigned_abs()
            .is_multiple_of(self.tick_size_price().value() as u64)
    }
    /// Returns `true` if, for this specific instrument, it is safe to use in orders.
    fn is_price_valid(&self, price: Price) -> bool {
        self.is_price_on_tick(price)
    }

    /// Returns `true` if `quantity >= min_qty`.
    fn is_qty_big_enough(&self, quantity: Quantity) -> bool {
        quantity >= self.min_quantity()
    }
    /// Returns `true` if `quantity.is_multiple_of(step_qty)`.
    fn is_qty_on_step(&self, quantity: Quantity) -> bool {
        quantity
            .value()
            .checked_sub(self.min_quantity().value())
            .is_some_and(|x| x.is_multiple_of(self.step_qty().step().value()))
    }
    /// Returns `true` if, for this specific instrument, it is safe to use in orders.
    fn is_qty_valid(&self, quantity: Quantity) -> bool {
        self.is_qty_big_enough(quantity) && self.is_qty_on_step(quantity)
    }

    // ---

    // --- Rounding

    /// Round price to tick size using half-away rounding.
    fn round_price(&self, price: Price) -> Option<Price> {
        todo!()
    }
    /// Round price up to tick size.
    fn round_up_price(&self, price: Price) -> Option<Price> {
        todo!()
    }
    /// Round price down to tick size.
    fn round_down_price(&self, price: Price) -> Option<Price> {
        todo!()
    }

    /// Round quantity to quantity_step using half-away rounding.
    fn round_quantity(&self, quantity: Quantity) -> Option<Quantity> {
        todo!()
    }
    /// Round quantity up to quantity_step.
    fn round_up_quantity(&self, quantity: Quantity) -> Option<Quantity> {
        todo!()
    }
    /// Round quantity down to quantity_step.
    fn round_down_quantity(&self, quantity: Quantity) -> Option<Quantity> {
        todo!()
    }

    // ---
}

/// Represents the essential trading specification parameters.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Specification {
    tick_size_price: Price,
    tick_size_currency: (Price, Currency),
    point_value: PointValue,
    min_quantity: Quantity,
    step_quantity: QtyStep,
}

impl Default for Specification {
    fn default() -> Self {
        Self {
            tick_size_price: Price::from_str_unchecked("0.01"),
            tick_size_currency: (Price::from_str_unchecked("0.01"), Currency::default()),
            point_value: PointValue::ONE,
            min_quantity: Quantity::ONE,
            step_quantity: QtyStep::default(),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum InvalidSpecification {
    PointValueNotRepresentable {
        tick_size_price: Price,
        tick_size_currency: (Price, Currency),
    },
    PointValueOutOfRange(i128),
    TickSizePrice(Price),
    ZeroMinQty,
}

impl Display for InvalidSpecification {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            InvalidSpecification::PointValueNotRepresentable {
                tick_size_price,
                tick_size_currency,
            } => {
                write!(
                    f,
                    "PointValueNotRepresentable {} / {} ({})",
                    tick_size_price, tick_size_currency.0, tick_size_currency.1
                )
            }
            InvalidSpecification::PointValueOutOfRange(out_of_range) => {
                write!(f, "PointValueOutOfRange {}", out_of_range)
            }
            InvalidSpecification::TickSizePrice(tick_size_price) => {
                write!(f, "TickSizePrice {}", tick_size_price)
            }
            InvalidSpecification::ZeroMinQty => write!(f, "Min quantity should not be zero"),
        }
    }
}

impl std::error::Error for InvalidSpecification {}

impl Specification {
    /// Builds a `Specification`, deriving `point_value` from the tick pair as
    /// `tick_size_currency.0 / tick_size_price`.
    ///
    /// # **Error-prone**: units are NOT verifiable
    ///
    /// Let's say that Currency has 2 forms: major and minor.
    /// We usually use major form: 2.13 ($)
    /// Minor form would use cents: 213 (cents)
    ///
    /// Usually `tick_size_currency` is in major form. At least I haven't seen
    /// a case where it's in minor form.
    ///
    /// But `tick_size_price` is in price quotation units and if price quotation in
    /// minor form - it should be in minor form. But, unfortunately, at least CME,
    /// can sometimes convert it to major form.
    ///
    /// Example of such case:
    /// - ZW - CME spec says its `tick_size_price` is 1/4 of a cent and write 0.0025
    ///   and you may think that you can just copy-paste its value like you do with other
    ///   futures contracts. But no, 1/4 of a cent is 0.25, but CME shows 0.0025 which is in major
    ///   form - wrong one, price is in minor.
    ///   So we should use 0.25. For an explanation, look at README.md, ZW example.
    ///   So the correct values are:
    ///   `(0.25, (12.5, USD))` - you can't copy-paste values from CME specification.
    ///
    /// So, fill a spec **once**, verify by hand and reuse specs.
    pub fn new(
        tick_size_price: Price,
        tick_size_currency: (Price, Currency),
        min_quantity: Quantity,
        step_quantity: QtyStep,
    ) -> Result<Self, InvalidSpecification> {
        if tick_size_price <= Price::ZERO || tick_size_price > Price::ONE {
            return Err(InvalidSpecification::TickSizePrice(tick_size_price));
        }
        if min_quantity == Quantity::ZERO {
            return Err(InvalidSpecification::ZeroMinQty);
        }
        let numerator = tick_size_currency.0.value() as i128 * PointValue::SCALE;
        let denominator = tick_size_price.value() as i128;
        // Not representable in 9 digits
        if numerator % denominator != 0 {
            return Err(InvalidSpecification::PointValueNotRepresentable {
                tick_size_price,
                tick_size_currency,
            });
        }
        let point_value = PointValue::new(numerator / denominator)
            .ok_or_else(|| InvalidSpecification::PointValueOutOfRange(numerator / denominator))?;

        Ok(Self {
            tick_size_price,
            tick_size_currency,
            point_value,
            min_quantity,
            step_quantity,
        })
    }

    pub fn min_quantity(&self) -> Quantity {
        self.min_quantity
    }
}

impl Spec for Specification {
    fn tick_size_price(&self) -> Price {
        self.tick_size_price
    }

    fn tick_size_currency(&self) -> (Price, Currency) {
        self.tick_size_currency
    }

    fn point_value(&self) -> PointValue {
        self.point_value
    }

    /// Convert `QuoteNotional` to `CurrencyNotional` using specification.
    fn currency_notional(&self, quote_notional: QuoteNotional) -> CurrencyNotional {
        // QuoteNotional is already half-away-rounded upstream,
        // so truncating the final divide only drops sub-1e-9 noise
        CurrencyNotional::new(
            QuoteNotional::round(self.point_value.0 * quote_notional.value()),
            self.tick_size_currency.1.into(),
        )
    }

    fn min_quantity(&self) -> Quantity {
        self.min_quantity
    }

    fn step_qty(&self) -> QtyStep {
        self.step_quantity
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PointValue(i128);

impl PointValue {
    pub const SCALE: i128 = Price::SCALE as i128;
    pub const PRECISION: u32 = Price::PRECISION;
    const POW10: [i128; Self::PRECISION as usize + 1] = [
        1,
        10,
        100,
        1_000,
        10_000,
        100_000,
        1_000_000,
        10_000_000,
        100_000_000,
        1_000_000_000,
    ];
    /// Max reference: JPY futures = 12.5 mil
    /// ```
    /// use tradeprim::quote_notional::QuoteNotional;
    ///
    /// pub const MAX_RAW: i128 = i128::MAX / QuoteNotional::MAX_RAW;
    /// assert_eq!(MAX_RAW, 34028195858252051);
    /// ```
    pub const MAX_RAW: i128 = i128::MAX / QuoteNotional::MAX_RAW;
    pub const MIN_RAW: i128 = 1_i128;
    pub const MAX_INTEGER_PART: i128 = Self::MAX_RAW / Self::SCALE;
    pub const MIN_INTEGER_PART: i128 = Self::MIN_RAW / Self::SCALE;

    pub const ONE: Self = Self::new_unchecked(Self::SCALE);
    pub const MAX: Self = Self::new_unchecked(Self::MAX_RAW);
    pub const MIN: Self = Self::new_unchecked(Self::MIN_RAW);

    /// Creates a new `PointValue` from a `Price`.
    /// Returns `None` if the price is not positive or greater than
    /// some reasonable amount.
    ///
    /// If `TickSize` is equal to `Price::ONE`, that means that
    /// `PointValue == TickSize` (common case for stock-like instruments)
    ///
    /// It's hard to argue about the maximum value of `PointValue`.
    /// For example, there is a JPY futures with point value of 12.5mil
    pub fn new(value: i128) -> Option<Self> {
        if !(Self::MIN_RAW..=Self::MAX_RAW).contains(&value) {
            return None;
        }
        Some(Self(value))
    }

    pub fn value(&self) -> i128 {
        self.0
    }

    const fn new_unchecked(value: i128) -> Self {
        Self(value)
    }

    pub fn from_str_unchecked(s: &str) -> Self {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, "000000000"));
        let is_negative = integer.starts_with('-');

        let parsed_integer = i128::from_str(integer).unwrap().abs();

        let used_precision = fraction.len();
        let remaining_precision = Self::PRECISION - used_precision as u32;
        let parsed_fraction = i128::from_str(fraction).unwrap();
        let adjusted_fraction = parsed_fraction * Self::POW10[remaining_precision as usize];

        let combined = match is_negative {
            true => -(parsed_integer * Self::SCALE + adjusted_fraction),
            false => parsed_integer * Self::SCALE + adjusted_fraction,
        };

        Self::new_unchecked(combined)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParsePointValueError {
    InvalidFormat,
    OutOfBounds,
    PrecisionError(usize),
    ParseIntError(ParseIntError),
}

impl Display for ParsePointValueError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParsePointValueError::InvalidFormat => write!(f, "Invalid format"),
            ParsePointValueError::OutOfBounds => write!(f, "Out of bounds"),
            ParsePointValueError::PrecisionError(precision) => {
                write!(f, "Precision error: {}", precision)
            }
            ParsePointValueError::ParseIntError(err) => err.fmt(f),
        }
    }
}

// --- Basically a copy-paste from a Price
impl FromStr for PointValue {
    type Err = ParsePointValueError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (integer, fraction) = s.split_once('.').unwrap_or((s, "000000000"));
        let (integer, fraction) = (integer.trim(), fraction.trim());
        // Check below needed to not accept and parse `-0.-1`
        // The fraction part would be parsed no problem
        if fraction.starts_with('-') || integer.starts_with('-') {
            return Err(ParsePointValueError::InvalidFormat);
        }

        let parsed_integer =
            i128::from_str(integer).map_err(ParsePointValueError::ParseIntError)?;
        if !(0..=Self::MAX_INTEGER_PART).contains(&parsed_integer) {
            return Err(ParsePointValueError::OutOfBounds);
        }

        let used_precision = fraction.len();
        if used_precision > Self::PRECISION as usize {
            return Err(ParsePointValueError::PrecisionError(used_precision));
        }
        let remaining_precision = Self::PRECISION - used_precision as u32;
        let parsed_fraction =
            i128::from_str(fraction).map_err(ParsePointValueError::ParseIntError)?;
        let adjusted_fraction = parsed_fraction * Self::POW10[remaining_precision as usize];
        let combined = parsed_integer * Self::SCALE + adjusted_fraction;
        if !(Self::MIN_RAW..=Self::MAX_RAW).contains(&combined) {
            return Err(ParsePointValueError::OutOfBounds);
        }

        Ok(Self::new_unchecked(combined))
    }
}

impl From<i128> for PointValue {
    fn from(value: i128) -> Self {
        Self::new(value).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::assert_matches;

    /// Canonical string for a non-negative `PointValue` raw value.
    fn pv_canonical(raw: i128) -> String {
        let int = raw / PointValue::SCALE;
        let frac = raw % PointValue::SCALE;
        if frac == 0 {
            format!("{int}")
        } else {
            format!("{int}.{}", format!("{frac:09}").trim_end_matches('0'))
        }
    }

    #[test]
    fn test_point_value_init() {
        assert!(PointValue::new(PointValue::MIN_RAW).is_some());
        assert!(PointValue::new(PointValue::MIN_RAW - 1).is_none());
        assert!(PointValue::new(PointValue::MAX_RAW).is_some());
        assert!(PointValue::new(PointValue::MAX_RAW + 1).is_none());
        assert!(
            PointValue::from_str("100")
                .is_ok_and(|x| x == PointValue::new_unchecked(100 * PointValue::SCALE))
        );
        assert!(
            PointValue::from_str("100.000000001")
                .is_ok_and(|x| x == PointValue::new_unchecked(100 * PointValue::SCALE + 1))
        );
        // --- Errors paths
        assert!(
            PointValue::from_str("-100").is_err_and(|x| x == ParsePointValueError::InvalidFormat)
        );
        assert_matches!(
            PointValue::from_str("1a.32").expect_err("Should fail with ParseIntError"),
            ParsePointValueError::ParseIntError(_)
        );
        assert_matches!(
            PointValue::from_str("10.3a").expect_err("Should fail with ParseIntError"),
            ParsePointValueError::ParseIntError(_)
        );
        assert!(
            PointValue::from_str("-100.000000001")
                .is_err_and(|x| x == ParsePointValueError::InvalidFormat)
        );
        let max_integer_part = (PointValue::MAX_INTEGER_PART + 1).to_string();
        assert!(
            PointValue::from_str(&max_integer_part)
                .is_err_and(|x| x == ParsePointValueError::OutOfBounds)
        );
        assert!(
            PointValue::from_str("100.0000000001")
                .is_err_and(|x| x == ParsePointValueError::PrecisionError(10))
        );
    }

    /// Zero is not a valid contract multiplier: `from_str` rejects it
    #[test]
    fn from_str_rejects_zero() {
        for s in ["0", "0.0", "0.000000000"] {
            assert_eq!(
                PointValue::from_str(s),
                Err(ParsePointValueError::OutOfBounds),
                "from_str({s:?}) must reject a zero point value"
            );
        }
    }

    #[test]
    fn from_str_accepts_endpoints() {
        // MIN_RAW == 1 raw == 0.000000001 (smallest strictly-positive value).
        let min = PointValue::from_str("0.000000001").expect("MIN_RAW must parse");
        assert_eq!(min.value(), PointValue::MIN_RAW);

        // MAX_RAW rendered canonically must round-trip exactly.
        let max =
            PointValue::from_str(&pv_canonical(PointValue::MAX_RAW)).expect("MAX_RAW must parse");
        assert_eq!(max.value(), PointValue::MAX_RAW);
    }

    #[test]
    fn from_str_rejects_above_max() {
        let s = format!("{}.999999999", PointValue::MAX_INTEGER_PART);
        assert_eq!(
            PointValue::from_str(&s),
            Err(ParsePointValueError::OutOfBounds),
            "from_str({s:?}) is above MAX_RAW"
        );
    }

    proptest! {
        /// Every in-range raw value roundtrips through `from_str`.
        #[test]
        fn from_str_roundtrips_in_range(raw in PointValue::MIN_RAW..=PointValue::MAX_RAW) {
            let s = pv_canonical(raw);
            prop_assert!(
                matches!(PointValue::from_str(&s), Ok(p) if p.value() == raw),
                "raw={raw} s={s}"
            );
        }

        /// Similar to `from_str_rejects_above_max`, but proptest
        #[test]
        fn from_str_rejects_overshoot_fraction(
            frac in (PointValue::MAX_RAW % PointValue::SCALE + 1)..PointValue::SCALE,
        ) {
            let s = format!("{}.{frac:09}", PointValue::MAX_INTEGER_PART);
            prop_assert_eq!(
                PointValue::from_str(&s),
                Err(ParsePointValueError::OutOfBounds),
                "s={}", s
            );
        }
    }

    #[test]
    fn specification_tests() {
        let min_qty = Quantity::ONE;
        // default case for a common shares
        // usd, cents
        let ts_p = Price::from_str_unchecked("0.01");
        let ts_c = (Price::from_str_unchecked("0.01"), Currency::default());
        let spec = Specification::new(ts_p, ts_c, min_qty, QtyStep::default()).unwrap();
        assert_eq!(ts_p, spec.tick_size_price());
        assert_eq!(ts_c.0, spec.tick_size_currency().0);
        assert_eq!(PointValue::from_str_unchecked("1.0"), spec.point_value());
        assert_eq!(spec.tick_size_currency.1, Currency::usd());

        // ZW, 5k bushels, price in cents, tick_size_currency in $
        // I had to multiply 0.0025 by 100...
        let spec = Specification::new(
            Price::from_str_unchecked("0.25"),
            (Price::from_str_unchecked("12.5"), Currency::usd()),
            min_qty,
            QtyStep::default(),
        )
        .unwrap();
        assert_eq!(Price::from_str_unchecked("0.25"), spec.tick_size_price());
        assert_eq!(
            Price::from_str_unchecked("12.5"),
            spec.tick_size_currency().0
        );
        assert_eq!(PointValue::from_str_unchecked("50.0"), spec.point_value());

        // RB, 42k gallons, price in dollars and cents, tick_size_currency in $
        let spec = Specification::new(
            Price::from_str_unchecked("0.0001"),
            (Price::from_str_unchecked("4.2"), Currency::usd()),
            min_qty,
            QtyStep::default(),
        )
        .unwrap();
        assert_eq!(Price::from_str_unchecked("0.0001"), spec.tick_size_price());
        assert_eq!(
            Price::from_str_unchecked("4.2"),
            spec.tick_size_currency().0
        );
        assert_eq!(
            PointValue::from_str_unchecked("42000.0"),
            spec.point_value()
        );

        // ZB, Face value at maturity of $100,000,
        // price Points and fractions of points with par on the basis of 100 points,
        // tick_size_currency in $
        let spec = Specification::new(
            Price::from_str_unchecked("0.03125"),
            (Price::from_str_unchecked("31.25"), Currency::usd()),
            min_qty,
            QtyStep::default(),
        )
        .unwrap();
        assert_eq!(Price::from_str_unchecked("0.03125"), spec.tick_size_price());
        assert_eq!(
            Price::from_str_unchecked("31.25"),
            spec.tick_size_currency().0
        );
        assert_eq!(PointValue::from_str_unchecked("1000.0"), spec.point_value());

        // 6J, contract_unit = 12,500,000 Japanese yen,
        // price U.S. dollars and cent per JPY increment,
        // 0.0000005 per JPY increment = $6.25
        let spec = Specification::new(
            Price::from_str_unchecked("0.0000005"),
            (Price::from_str_unchecked("6.25"), Currency::usd()),
            min_qty,
            QtyStep::default(),
        )
        .unwrap();
        assert_eq!(
            Price::from_str_unchecked("0.0000005"),
            spec.tick_size_price()
        );
        assert_eq!(
            Price::from_str_unchecked("6.25"),
            spec.tick_size_currency().0
        );
        assert_eq!(
            PointValue::from_str_unchecked("12500000.0"),
            spec.point_value()
        );
    }

    /// - `tick_size_price` is in `(0, Price::ONE)`
    /// - `tick_size_price` that is `Price::ONE` accepted
    /// - `tick_size_price = Price::ONE + min increment` - not accepted
    #[test]
    fn new_tick_size_price_boundary() {
        let usd = (Price::ONE, Currency::usd());

        // Below the range: zero tick would divide by zero deriving point_value.
        assert_eq!(
            Specification::new(Price::ZERO, usd, Quantity::ONE, QtyStep::default()),
            Err(InvalidSpecification::TickSizePrice(Price::ZERO))
        );
        // assert!(
        //     Specification::new(Price::ZERO, usd, Quantity::ONE, QtyStep::default()),
        //     "tick_size_price = 0 must be rejected"
        // );

        // Upper edge is inclusive: exactly one whole price unit is valid.
        assert!(
            Specification::new(Price::ONE, usd, Quantity::ONE, QtyStep::default()).is_ok(),
            "tick_size_price == Price::ONE must be accepted"
        );

        // One raw step above the edge: not a valid tick.
        let above_one = Price::from_str_unchecked("1.000000001");
        assert_eq!(
            Specification::new(above_one, usd, Quantity::ONE, QtyStep::default()),
            Err(InvalidSpecification::TickSizePrice(above_one))
        );
        // assert!(
        //     Specification::new(above_one, usd, Quantity::ONE, QtyStep::default()).is_none(),
        //     "tick_size_price > Price::ONE must be rejected"
        // );
    }

    #[test]
    fn test_currency_notional() {
        // ZB, Face value at maturity of $100,000,
        // price Points and fractions of points with par on the basis of 100 points,
        // tick_size_currency in $
        let spec = Specification::new(
            Price::from_str_unchecked("0.03125"),
            (Price::from_str_unchecked("31.25"), Currency::usd()),
            Quantity::ONE,
            QtyStep::default(),
        )
        .unwrap();
        let qn = QuoteNotional::from_str_unchecked("552.8125");
        let cn = spec.currency_notional(qn);

        // Readme example, should be equal to 552_812.5
        assert_eq!(
            cn,
            CurrencyNotional::new(552_812_500_000_000, Currency::usd().into())
        );

        // 6J, contract_unit = 12,500,000 Japanese yen,
        // price U.S. dollars and cent per JPY increment,
        // 0.0000005 per JPY increment = $6.25
        //
        // ($ / JPY, $ / contract)
        // pv = JPY / contract
        // qn = contract * $ / JPY
        // cn = pv * qn = JPY / contract * contract * $ / JPY
        // cn = $
        //
        // let qty = 5, let px = 0.006125
        // qn = 5 * 0.006125 = 0.030625
        // pv = 12_500_000.0
        // cn = pv * qn = 12_500_000 * 0.030625 = 382812.5
        let spec = Specification::new(
            Price::from_str_unchecked("0.0000005"),
            (Price::from_str_unchecked("6.25"), Currency::usd()),
            Quantity::ONE,
            QtyStep::default(),
        )
        .unwrap();
        let qn = QuoteNotional::from_str_unchecked("0.030625");
        let cn = spec.currency_notional(qn);
        assert_eq!(
            cn,
            CurrencyNotional::new(382812500000000, Currency::usd().into())
        )
    }

    /// `currency_notional` must round its final divide to the nearest 1e-9,
    /// not truncate (I was wrong :/ ).
    ///
    /// point_value = 0.95 / 0.5 = 1.9 (exact).
    ///
    /// With qn = 1e-9 the true product is 1.9e-9,
    /// whose nearest 1e-9 is 2e-9 — truncation would give 1e-9.
    ///
    /// This should never happen in real life though.
    #[test]
    fn currency_notional_rounds_to_nearest_positive() {
        let spec = Specification::new(
            Price::from_str_unchecked("0.5"),
            (Price::from_str_unchecked("0.95"), Currency::usd()),
            Quantity::ONE,
            QtyStep::default(),
        )
        .unwrap();
        let qn = QuoteNotional::from_str_unchecked("0.000000001");
        assert_eq!(
            spec.currency_notional(qn),
            CurrencyNotional::new(2, Currency::usd().into()),
            "1.9e-9 must round to 2e-9, not to 1e-9"
        );
    }

    /// Same magnitude, opposite sign.
    #[test]
    fn currency_notional_rounds_symmetrically_for_negatives() {
        let spec = Specification::new(
            Price::from_str_unchecked("0.5"),
            (Price::from_str_unchecked("0.95"), Currency::usd()),
            Quantity::ONE,
            QtyStep::default(),
        )
        .unwrap();
        let qn = QuoteNotional::from_str_unchecked("-0.000000001");
        assert_eq!(
            spec.currency_notional(qn),
            CurrencyNotional::new(-2, Currency::usd().into()),
            "-1.9e-9 must round to -2e-9, symmetric with the positive case"
        );
    }

    /// A spec whose `point_value` (`tick_size_currency.0 / tick_size_price`)
    /// does not terminate within 9 digits must be rejected at construction,
    /// rather than silently truncating and losing a ULP downstream.
    ///
    /// This should never happen in real life though.
    #[test]
    fn new_rejects_non_terminating_point_value() {
        // 0.01 / 0.03 = 1/3 — not representable in 9-digit fixed point.
        let tsp = Price::from_str_unchecked("0.03");
        let tsc = (Price::from_str_unchecked("0.01"), Currency::usd());
        assert_eq!(
            Specification::new(tsp, tsc, Quantity::ONE, QtyStep::default()),
            Err(InvalidSpecification::PointValueNotRepresentable {
                tick_size_price: tsp,
                tick_size_currency: tsc,
            })
        );
        // assert!(
        //     Specification::new(
        //         Price::from_str_unchecked("0.03"),
        //         (Price::from_str_unchecked("0.01"), Currency::usd()),
        //         Quantity::ONE,
        //         QtyStep::default()
        //     )
        //     .is_none(),
        //     "non-terminating tick ratio must be rejected"
        // );
    }

    /// A tick pair that divides exactly but lands outside `PointValue`'s range.
    /// Both ends are reachable, and the error must carry the raw quotient.
    #[test]
    fn new_rejects_out_of_range_point_value() {
        // Below MIN_RAW (== 1): an unfilled `tick_size_currency` divides to 0.
        let tsp = Price::ONE;
        let tsc = (Price::ZERO, Currency::usd());
        assert_eq!(
            Specification::new(tsp, tsc, Quantity::ONE, QtyStep::default()),
            Err(InvalidSpecification::PointValueOutOfRange(0)),
            "a zero currency tick is out of range, not a division failure"
        );

        // Above MAX_RAW: 1.0 / 1e-9 = 1e9 points.
        let tsp = Price::from_str_unchecked("0.000000001");
        let tsc = (Price::ONE, Currency::usd());
        assert_eq!(
            Specification::new(tsp, tsc, Quantity::ONE, QtyStep::default()),
            Err(InvalidSpecification::PointValueOutOfRange(
                1_000_000_000_000_000_000
            ))
        );
    }

    /// ZW-spec with the quantity grid as the parameter under test.
    fn zw_spec_with(min_quantity: &str, step: &str) -> Specification {
        Specification::new(
            Price::from_str_unchecked("0.25"),
            (Price::from_str_unchecked("12.5"), Currency::usd()),
            Quantity::from_str_unchecked(min_quantity),
            QtyStep::new(Quantity::from_str_unchecked(step)).expect("step must be non-zero"),
        )
        .expect("ZW tick pair is valid")
    }

    /// The grid is anchored at `min_quantity`: valid sizes are `min + k*step`.
    #[test]
    fn quantity_grid_is_anchored_at_the_minimum() {
        let spec = zw_spec_with("10", "3");
        assert!(spec.is_qty_valid(Quantity::from_str_unchecked("10")));
        assert!(spec.is_qty_valid(Quantity::from_str_unchecked("13")));
        assert!(
            !spec.is_qty_valid(Quantity::from_str_unchecked("12")),
            "12 is a multiple of 3 but is not on the offset grid"
        );
    }

    /// `min - step` would be on the grid, but below `min`, so it should not.
    #[test]
    fn below_min_is_neither_big_enough_nor_on_step() {
        let spec = zw_spec_with("10", "3");
        let q = Quantity::from_str_unchecked("7");
        assert!(!spec.is_qty_big_enough(q));
        // main check - it's not on the grid
        assert!(
            !spec.is_qty_on_step(q),
            "no grid point exists below the minimum"
        );
    }

    /// Tick checks must survive zero/negative prices.
    #[test]
    fn negative_price_is_checked_against_the_tick() {
        let spec = zw_spec_with("1", "1");
        assert!(spec.is_price_on_tick(Price::from_str_unchecked("-0.5")));
        assert!(!spec.is_price_on_tick(Price::from_str_unchecked("-0.6")));
        assert!(spec.is_price_on_tick(Price::ZERO));
    }

    /// Zero quantity orders are not allowed, that's why we reject such spec
    #[test]
    fn new_spec_rejects_min_zero_quantity() {
        assert_eq!(
            Specification::new(
                Price::from_str_unchecked("0.25"),
                (Price::from_str_unchecked("12.5"), Currency::usd()),
                Quantity::from_str_unchecked("0"),
                QtyStep::new(Quantity::from_str_unchecked("3")).expect("step must be non-zero"),
            ),
            Err(InvalidSpecification::ZeroMinQty)
        );
    }
}
