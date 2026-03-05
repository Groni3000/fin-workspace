use std::ops::{Add, Neg, Sub};

use instrid::future::Future;
use instrid::option_contract::OptionContract;

use crate::schedule::ListingSchedule;

/// An offset by years and/or listed tenors, forward or backward.
///
/// Separating `years` from `listed_tenors` makes common offsets expressive:
/// - "next contract" → `ContractOffset::tenors(1)`
/// - "same month next year" → `ContractOffset::years(1)`
/// - "2 years and 1 tenor forward" → `ContractOffset::new(2, 1)`
///
/// # Examples
/// ```
/// use fin_futures::offset::ContractOffset;
/// use fin_futures::schedule::ListingSchedule;
/// use instrid::future::Future;
/// use instrid::tenor::Tenor;
///
/// let schedule = ListingSchedule::quarterly();
/// let es_jun: Future = "ES/USD@CME#2025-JUN".parse().unwrap();
///
/// let next = ContractOffset::tenors(1).apply(&es_jun, &schedule);
/// assert_eq!(next.month, Tenor::September);
/// assert_eq!(next.year, 2025);
///
/// let rolled = ContractOffset::tenors(2).apply(&es_jun, &schedule);
/// assert_eq!(rolled.month, Tenor::December);
/// assert_eq!(rolled.year, 2025);
///
/// let next_year = ContractOffset::years(1).apply(&es_jun, &schedule);
/// assert_eq!(next_year.month, Tenor::June);
/// assert_eq!(next_year.year, 2026);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContractOffset {
    pub years: i32,
    pub listed_tenors: i32,
}

impl ContractOffset {
    /// Creates an offset with explicit year and tenor components.
    pub fn new(years: i32, listed_tenors: i32) -> Self {
        Self { years, listed_tenors }
    }

    /// Offset by `n` listed tenors (positive = forward, negative = backward).
    pub fn tenors(n: i32) -> Self {
        Self { years: 0, listed_tenors: n }
    }

    /// Offset by `n` years (positive = forward, negative = backward).
    pub fn years(n: i32) -> Self {
        Self { years: n, listed_tenors: 0 }
    }

    /// Applies this offset to a future, returning a new future with adjusted year/month.
    ///
    /// The instrument, day, and multiplier are preserved from the original.
    ///
    /// # Panics
    /// Panics if the future's month is not in the schedule.
    pub fn apply(&self, future: &Future, schedule: &ListingSchedule) -> Future {
        let (year, month) = advance(future.year, future.month, self, schedule);
        Future::new(future.instrument, year, month, future.day, future.multiplier)
    }

    /// Applies this offset to an option contract, returning a new one with adjusted year/month.
    ///
    /// The instrument, day, multiplier, option type, and strike are preserved.
    ///
    /// # Panics
    /// Panics if the option's month is not in the schedule.
    pub fn apply_option(
        &self,
        option: &OptionContract,
        schedule: &ListingSchedule,
    ) -> OptionContract {
        let (year, month) = advance(option.year, option.month, self, schedule);
        OptionContract::new(
            option.instrument,
            year,
            month,
            option.day,
            option.multiplier,
            option.option_type,
            option.strike,
        )
    }
}

impl Add for ContractOffset {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self {
            years: self.years + rhs.years,
            listed_tenors: self.listed_tenors + rhs.listed_tenors,
        }
    }
}

impl Sub for ContractOffset {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self {
            years: self.years - rhs.years,
            listed_tenors: self.listed_tenors - rhs.listed_tenors,
        }
    }
}

impl Neg for ContractOffset {
    type Output = Self;
    fn neg(self) -> Self {
        Self {
            years: -self.years,
            listed_tenors: -self.listed_tenors,
        }
    }
}

/// Advances (or retreats) from a given year/month using O(1) divmod arithmetic.
fn advance(
    year: u16,
    month: instrid::tenor::Tenor,
    offset: &ContractOffset,
    schedule: &ListingSchedule,
) -> (u16, instrid::tenor::Tenor) {
    let tenors = schedule.tenors();
    let len = tenors.len() as i32;
    let current_index = schedule
        .index_of(&month)
        .expect("month must be in schedule") as i32;

    let new_abs = current_index + offset.listed_tenors;
    let additional_years = new_abs.div_euclid(len);
    let new_index = new_abs.rem_euclid(len);

    let new_tenor = tenors[new_index as usize];
    let new_year = (year as i32) + offset.years + additional_years;

    (new_year as u16, new_tenor)
}

#[cfg(test)]
mod tests {
    use super::*;
    use instrid::tenor::Tenor;

    fn parse_future(s: &str) -> Future {
        s.parse().unwrap()
    }

    fn parse_option(s: &str) -> OptionContract {
        s.parse().unwrap()
    }

    // region: construction

    #[test]
    fn tenors_constructor() {
        let off = ContractOffset::tenors(3);
        assert_eq!(off.years, 0);
        assert_eq!(off.listed_tenors, 3);
    }

    #[test]
    fn years_constructor() {
        let off = ContractOffset::years(2);
        assert_eq!(off.years, 2);
        assert_eq!(off.listed_tenors, 0);
    }

    #[test]
    fn new_constructor() {
        let off = ContractOffset::new(1, -2);
        assert_eq!(off.years, 1);
        assert_eq!(off.listed_tenors, -2);
    }

    // endregion

    // region: arithmetic on offsets

    #[test]
    fn add_offsets() {
        let a = ContractOffset::new(1, 2);
        let b = ContractOffset::new(3, -1);
        let sum = a + b;
        assert_eq!(sum, ContractOffset::new(4, 1));
    }

    #[test]
    fn sub_offsets() {
        let a = ContractOffset::new(3, 5);
        let b = ContractOffset::new(1, 2);
        let diff = a - b;
        assert_eq!(diff, ContractOffset::new(2, 3));
    }

    #[test]
    fn neg_offset() {
        let off = ContractOffset::new(2, -3);
        assert_eq!(-off, ContractOffset::new(-2, 3));
    }

    // endregion

    // region: apply to Future — forward

    #[test]
    fn forward_one_quarterly() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-JUN");
        let next = ContractOffset::tenors(1).apply(&fut, &schedule);
        assert_eq!(next.month, Tenor::September);
        assert_eq!(next.year, 2025);
    }

    #[test]
    fn forward_wraps_year() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-DEC");
        let next = ContractOffset::tenors(1).apply(&fut, &schedule);
        assert_eq!(next.month, Tenor::March);
        assert_eq!(next.year, 2026);
    }

    #[test]
    fn forward_multiple_years() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-MAR");
        // 4 quarterly steps = one full year
        let next = ContractOffset::tenors(4).apply(&fut, &schedule);
        assert_eq!(next.month, Tenor::March);
        assert_eq!(next.year, 2026);
    }

    #[test]
    fn forward_monthly() {
        let schedule = ListingSchedule::monthly();
        let fut = parse_future("CL/USD@NYMEX#2025-NOV");
        let next = ContractOffset::tenors(3).apply(&fut, &schedule);
        assert_eq!(next.month, Tenor::February);
        assert_eq!(next.year, 2026);
    }

    #[test]
    fn forward_zero_is_identity() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-JUN");
        let same = ContractOffset::tenors(0).apply(&fut, &schedule);
        assert_eq!(same.year, 2025);
        assert_eq!(same.month, Tenor::June);
    }

    // endregion

    // region: apply to Future — backward

    #[test]
    fn backward_one_quarterly() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-SEP");
        let prev = ContractOffset::tenors(-1).apply(&fut, &schedule);
        assert_eq!(prev.month, Tenor::June);
        assert_eq!(prev.year, 2025);
    }

    #[test]
    fn backward_wraps_year() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-MAR");
        let prev = ContractOffset::tenors(-1).apply(&fut, &schedule);
        assert_eq!(prev.month, Tenor::December);
        assert_eq!(prev.year, 2024);
    }

    #[test]
    fn backward_multiple_years() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-MAR");
        let prev = ContractOffset::tenors(-5).apply(&fut, &schedule);
        assert_eq!(prev.month, Tenor::December);
        assert_eq!(prev.year, 2023);
    }

    // endregion

    // region: years offset

    #[test]
    fn years_offset_same_month() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-JUN");
        let next_year = ContractOffset::years(1).apply(&fut, &schedule);
        assert_eq!(next_year.month, Tenor::June);
        assert_eq!(next_year.year, 2026);
    }

    #[test]
    fn years_and_tenors_combined() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-JUN");
        // 1 year + 1 tenor = Sep 2026
        let result = ContractOffset::new(1, 1).apply(&fut, &schedule);
        assert_eq!(result.month, Tenor::September);
        assert_eq!(result.year, 2026);
    }

    #[test]
    fn negative_years() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-JUN");
        let prev_year = ContractOffset::years(-1).apply(&fut, &schedule);
        assert_eq!(prev_year.month, Tenor::June);
        assert_eq!(prev_year.year, 2024);
    }

    // endregion

    // region: preserves fields

    #[test]
    fn preserves_instrument_day_multiplier() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-JUN-15*50");
        let next = ContractOffset::tenors(1).apply(&fut, &schedule);
        assert_eq!(next.instrument, fut.instrument);
        assert_eq!(next.day, Some(15));
        assert_eq!(next.multiplier, Some(50.0));
        assert_eq!(next.month, Tenor::September);
    }

    // endregion

    // region: apply to OptionContract

    #[test]
    fn option_forward() {
        let schedule = ListingSchedule::quarterly();
        let opt = parse_option("ES/USD@CME#2025-JUN:CALL$4500");
        let next = ContractOffset::tenors(1).apply_option(&opt, &schedule);
        assert_eq!(next.month, Tenor::September);
        assert_eq!(next.year, 2025);
        assert_eq!(next.strike, 4500.0);
        assert_eq!(next.option_type, opt.option_type);
    }

    #[test]
    fn option_backward_wraps() {
        let schedule = ListingSchedule::quarterly();
        let opt = parse_option("ES/USD@CME#2025-MAR:PUT$4000");
        let prev = ContractOffset::tenors(-1).apply_option(&opt, &schedule);
        assert_eq!(prev.month, Tenor::December);
        assert_eq!(prev.year, 2024);
        assert_eq!(prev.strike, 4000.0);
    }

    // endregion

    // region: large offsets (O(1) verification)

    #[test]
    fn large_forward_offset() {
        let schedule = ListingSchedule::quarterly();
        let fut = parse_future("ES/USD@CME#2025-MAR");
        // 100 quarterly steps = 25 years
        let result = ContractOffset::tenors(100).apply(&fut, &schedule);
        assert_eq!(result.month, Tenor::March);
        assert_eq!(result.year, 2050);
    }

    #[test]
    fn large_backward_offset() {
        let schedule = ListingSchedule::monthly();
        let fut = parse_future("CL/USD@NYMEX#2025-JAN");
        // -120 monthly steps = 10 years back
        let result = ContractOffset::tenors(-120).apply(&fut, &schedule);
        assert_eq!(result.month, Tenor::January);
        assert_eq!(result.year, 2015);
    }

    // endregion
}
