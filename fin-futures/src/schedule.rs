use instrid::tenor::Tenor;

/// Defines which contract months (tenors) are listed for a given product.
///
/// Different products list contracts in different months. For example,
/// equity index futures (ES, NQ) typically list quarterly months
/// (Mar, Jun, Sep, Dec), while energy futures (CL) list every month.
///
/// # Examples
/// ```
/// use fin_futures::schedule::ListingSchedule;
/// use instrid::tenor::Tenor;
///
/// let quarterly = ListingSchedule::quarterly();
/// assert_eq!(quarterly.tenors(), &[Tenor::March, Tenor::June, Tenor::September, Tenor::December]);
///
/// let (next, rolled) = quarterly.next_tenor(Tenor::June);
/// assert_eq!(next, Tenor::September);
/// assert!(!rolled);
///
/// let (next, rolled) = quarterly.next_tenor(Tenor::December);
/// assert_eq!(next, Tenor::March);
/// assert!(rolled);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ListingSchedule {
    tenors: Vec<Tenor>,
}

impl ListingSchedule {
    /// Creates a new schedule from a slice of tenors.
    ///
    /// The tenors are sorted and deduplicated.
    ///
    /// # Panics
    /// Panics if `tenors` is empty.
    pub fn new(tenors: &[Tenor]) -> Self {
        assert!(!tenors.is_empty(), "ListingSchedule must have at least one tenor");
        let mut sorted: Vec<Tenor> = tenors.to_vec();
        sorted.sort();
        sorted.dedup();
        Self { tenors: sorted }
    }

    /// All 12 months listed.
    pub fn monthly() -> Self {
        Self {
            tenors: vec![
                Tenor::January,
                Tenor::February,
                Tenor::March,
                Tenor::April,
                Tenor::May,
                Tenor::June,
                Tenor::July,
                Tenor::August,
                Tenor::September,
                Tenor::October,
                Tenor::November,
                Tenor::December,
            ],
        }
    }

    /// Quarterly months: March, June, September, December.
    pub fn quarterly() -> Self {
        Self {
            tenors: vec![
                Tenor::March,
                Tenor::June,
                Tenor::September,
                Tenor::December,
            ],
        }
    }

    /// Returns the listed tenors in calendar order.
    pub fn tenors(&self) -> &[Tenor] {
        &self.tenors
    }

    /// Returns true if the given tenor is in this schedule.
    pub fn contains(&self, tenor: &Tenor) -> bool {
        self.tenors.contains(tenor)
    }

    /// Returns the index of `tenor` in the schedule, or `None` if not listed.
    pub fn index_of(&self, tenor: &Tenor) -> Option<usize> {
        self.tenors.iter().position(|t| t == tenor)
    }

    /// Returns the number of listed tenors.
    pub fn len(&self) -> usize {
        self.tenors.len()
    }

    /// Returns the next listed tenor after `tenor`, and whether the year rolled over.
    ///
    /// If `tenor` is at or past the last listed month, wraps to the first listed
    /// month and returns `rolled = true`.
    pub fn next_tenor(&self, tenor: Tenor) -> (Tenor, bool) {
        // Find the first tenor strictly after the given one
        for &t in &self.tenors {
            if t > tenor {
                return (t, false);
            }
        }
        // Wrapped past December — return first tenor, year rolls over
        (self.tenors[0], true)
    }

    /// Returns the previous listed tenor before `tenor`, and whether the year rolled back.
    ///
    /// If `tenor` is at or before the first listed month, wraps to the last listed
    /// month and returns `rolled = true`.
    pub fn prev_tenor(&self, tenor: Tenor) -> (Tenor, bool) {
        // Find the last tenor strictly before the given one
        for &t in self.tenors.iter().rev() {
            if t < tenor {
                return (t, false);
            }
        }
        // Wrapped past January — return last tenor, year rolls back
        (*self.tenors.last().unwrap(), true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // region: construction

    #[test]
    fn new_sorts_and_deduplicates() {
        let schedule = ListingSchedule::new(&[
            Tenor::December,
            Tenor::March,
            Tenor::March,
            Tenor::June,
        ]);
        assert_eq!(
            schedule.tenors(),
            &[Tenor::March, Tenor::June, Tenor::December]
        );
    }

    #[test]
    #[should_panic(expected = "at least one tenor")]
    fn new_empty_panics() {
        ListingSchedule::new(&[]);
    }

    #[test]
    fn monthly_has_12_tenors() {
        let schedule = ListingSchedule::monthly();
        assert_eq!(schedule.tenors().len(), 12);
        assert_eq!(schedule.tenors()[0], Tenor::January);
        assert_eq!(schedule.tenors()[11], Tenor::December);
    }

    #[test]
    fn quarterly_has_4_tenors() {
        let schedule = ListingSchedule::quarterly();
        assert_eq!(
            schedule.tenors(),
            &[Tenor::March, Tenor::June, Tenor::September, Tenor::December]
        );
    }

    // endregion

    // region: contains

    #[test]
    fn contains_listed_tenor() {
        let schedule = ListingSchedule::quarterly();
        assert!(schedule.contains(&Tenor::March));
        assert!(schedule.contains(&Tenor::December));
    }

    #[test]
    fn does_not_contain_unlisted_tenor() {
        let schedule = ListingSchedule::quarterly();
        assert!(!schedule.contains(&Tenor::January));
        assert!(!schedule.contains(&Tenor::February));
        assert!(!schedule.contains(&Tenor::July));
    }

    // endregion

    // region: index_of / len

    #[test]
    fn index_of_listed() {
        let schedule = ListingSchedule::quarterly();
        assert_eq!(schedule.index_of(&Tenor::March), Some(0));
        assert_eq!(schedule.index_of(&Tenor::June), Some(1));
        assert_eq!(schedule.index_of(&Tenor::September), Some(2));
        assert_eq!(schedule.index_of(&Tenor::December), Some(3));
    }

    #[test]
    fn index_of_unlisted() {
        let schedule = ListingSchedule::quarterly();
        assert_eq!(schedule.index_of(&Tenor::January), None);
        assert_eq!(schedule.index_of(&Tenor::July), None);
    }

    #[test]
    fn len_quarterly() {
        assert_eq!(ListingSchedule::quarterly().len(), 4);
    }

    #[test]
    fn len_monthly() {
        assert_eq!(ListingSchedule::monthly().len(), 12);
    }

    // endregion

    // region: next_tenor

    #[test]
    fn next_tenor_within_year() {
        let schedule = ListingSchedule::quarterly();
        let (next, rolled) = schedule.next_tenor(Tenor::March);
        assert_eq!(next, Tenor::June);
        assert!(!rolled);
    }

    #[test]
    fn next_tenor_wraps_year() {
        let schedule = ListingSchedule::quarterly();
        let (next, rolled) = schedule.next_tenor(Tenor::December);
        assert_eq!(next, Tenor::March);
        assert!(rolled);
    }

    #[test]
    fn next_tenor_from_unlisted_month() {
        let schedule = ListingSchedule::quarterly();
        // January is not listed; next listed is March
        let (next, rolled) = schedule.next_tenor(Tenor::January);
        assert_eq!(next, Tenor::March);
        assert!(!rolled);
    }

    #[test]
    fn next_tenor_from_between_listed() {
        let schedule = ListingSchedule::quarterly();
        // July is between June and September
        let (next, rolled) = schedule.next_tenor(Tenor::July);
        assert_eq!(next, Tenor::September);
        assert!(!rolled);
    }

    #[test]
    fn next_tenor_monthly_simple() {
        let schedule = ListingSchedule::monthly();
        let (next, rolled) = schedule.next_tenor(Tenor::June);
        assert_eq!(next, Tenor::July);
        assert!(!rolled);
    }

    #[test]
    fn next_tenor_monthly_wraps() {
        let schedule = ListingSchedule::monthly();
        let (next, rolled) = schedule.next_tenor(Tenor::December);
        assert_eq!(next, Tenor::January);
        assert!(rolled);
    }

    // endregion

    // region: prev_tenor

    #[test]
    fn prev_tenor_within_year() {
        let schedule = ListingSchedule::quarterly();
        let (prev, rolled) = schedule.prev_tenor(Tenor::December);
        assert_eq!(prev, Tenor::September);
        assert!(!rolled);
    }

    #[test]
    fn prev_tenor_wraps_year() {
        let schedule = ListingSchedule::quarterly();
        let (prev, rolled) = schedule.prev_tenor(Tenor::March);
        assert_eq!(prev, Tenor::December);
        assert!(rolled);
    }

    #[test]
    fn prev_tenor_from_unlisted_month() {
        let schedule = ListingSchedule::quarterly();
        // November is between September and December
        let (prev, rolled) = schedule.prev_tenor(Tenor::November);
        assert_eq!(prev, Tenor::September);
        assert!(!rolled);
    }

    #[test]
    fn prev_tenor_wraps_from_before_first() {
        let schedule = ListingSchedule::quarterly();
        // January is before March (first listed)
        let (prev, rolled) = schedule.prev_tenor(Tenor::January);
        assert_eq!(prev, Tenor::December);
        assert!(rolled);
    }

    // endregion

    // region: single-tenor schedule

    #[test]
    fn single_tenor_next_wraps() {
        let schedule = ListingSchedule::new(&[Tenor::June]);
        let (next, rolled) = schedule.next_tenor(Tenor::June);
        assert_eq!(next, Tenor::June);
        assert!(rolled);
    }

    #[test]
    fn single_tenor_prev_wraps() {
        let schedule = ListingSchedule::new(&[Tenor::June]);
        let (prev, rolled) = schedule.prev_tenor(Tenor::June);
        assert_eq!(prev, Tenor::June);
        assert!(rolled);
    }

    // endregion
}
