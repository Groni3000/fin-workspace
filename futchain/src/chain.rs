use instrid::prelude::FuturesContract;

use crate::listing::ListedTenors;

#[derive(Debug)]
pub struct FutChain<'a> {
    cursor: FuturesContract,
    listing: &'a ListedTenors,
}

#[derive(Debug, PartialEq)]
pub enum FutChainError {
    ContractTenorNotListed,
}

impl<'a> FutChain<'a> {
    pub fn new(
        contract: FuturesContract,
        listing: &'a ListedTenors,
    ) -> Result<Self, FutChainError> {
        if !listing.contains(contract.tenor()) {
            return Err(FutChainError::ContractTenorNotListed);
        }

        Ok(Self {
            cursor: contract,
            listing,
        })
    }

    pub fn contract(&self) -> &FuturesContract {
        &self.cursor
    }

    pub fn listed_tenors(&self) -> &ListedTenors {
        self.listing
    }

    pub fn advance(&mut self) {
        let listing = self.listing;
        let idx = listing
            .find(&self.cursor.tenor())
            .expect("invariant: cursor.tenor() is in listing");
        let next_idx = (idx + 1) % listing.len();
        // wrap => next year
        let additional_year = if next_idx < idx { 1 } else { 0 };
        let next_tenor = listing
            .nth(next_idx)
            .expect("invariant: next tenor is in listing");
        self.cursor = self.cursor.with_year_tenor(
            self.cursor
                .year()
                .checked_add(additional_year)
                .expect("year overflow on advance"),
            next_tenor,
        );
    }

    /// Advance the cursor `n` times. `n == 0` is a no-op.
    ///
    /// Implemented as a simple loop over [`advance`](Self::advance). For typical
    /// `n` (tens to hundreds, e.g. backtest windows) this is microseconds. If
    /// profiling ever shows this in a hot loop, swap the body for one-shot
    /// modular math — the API stays identical. Until then, we prefer reuse over
    /// bloating already-busy code.
    pub fn advance_by(&mut self, n: usize) {
        for _ in 0..n {
            self.advance();
        }
    }

    pub fn retreat(&mut self) {
        let listing = self.listing;
        let idx = listing
            .find(&self.cursor.tenor())
            .expect("invariant: cursor.tenor() is in listing");
        // if idx == 0 => idx - 1 means error => checked_sub
        let next_idx = idx.checked_sub(1).unwrap_or(listing.len() - 1);
        // wrap => previous year
        let excess_year = if next_idx > idx { 1 } else { 0 };
        let next_tenor = listing
            .nth(next_idx)
            .expect("invariant: next tenor is in listing");
        self.cursor = self.cursor.with_year_tenor(
            self.cursor
                .year()
                .checked_sub(excess_year)
                .expect("year underflow on retreat"),
            next_tenor,
        );
    }

    /// Retreat the cursor `n` times. `n == 0` is a no-op.
    ///
    /// Implemented as a simple loop over [`retreat`](Self::retreat). Same
    /// trade-off as [`advance_by`](Self::advance_by) — if it ever shows up in a
    /// hot loop we'll swap the body for one-shot modular math, but realistically
    /// it won't, and reuse beats bloat in already-busy code.
    pub fn retreat_by(&mut self, n: usize) {
        for _ in 0..n {
            self.retreat();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::listing::ListedTenors;
    use instrid::prelude::{Asset, AssetClass, Mic, Tenor};

    fn es(year: u16, tenor: Tenor, day: Option<u8>) -> FuturesContract {
        FuturesContract::new(
            Asset::new("ES", AssetClass::Index),
            Asset::new("USD", AssetClass::Currency),
            Mic::xcme(),
            year,
            tenor,
            day,
        )
    }

    #[test]
    fn advance_within_year() {
        let listing = ListedTenors::quarterly();
        let mut chain = FutChain::new(es(2026, Tenor::March, None), &listing).unwrap();
        chain.advance();
        assert_eq!(chain.contract().tenor(), Tenor::June);
        assert_eq!(chain.contract().year(), 2026);
    }

    #[test]
    fn advance_wraps_year() {
        let listing = ListedTenors::quarterly();
        let mut chain = FutChain::new(es(2026, Tenor::December, None), &listing).unwrap();
        chain.advance();
        assert_eq!(chain.contract().tenor(), Tenor::March);
        assert_eq!(chain.contract().year(), 2027);
    }

    #[test]
    fn retreat_within_year() {
        let listing = ListedTenors::quarterly();
        let mut chain = FutChain::new(es(2026, Tenor::June, None), &listing).unwrap();
        chain.retreat();
        assert_eq!(chain.contract().tenor(), Tenor::March);
        assert_eq!(chain.contract().year(), 2026);
    }

    #[test]
    fn retreat_wraps_year() {
        let listing = ListedTenors::quarterly();
        let mut chain = FutChain::new(es(2026, Tenor::March, None), &listing).unwrap();
        chain.retreat();
        assert_eq!(chain.contract().tenor(), Tenor::December);
        assert_eq!(chain.contract().year(), 2025);
    }

    #[test]
    fn advance_then_retreat_returns_to_origin() {
        let listing = ListedTenors::quarterly();
        let start = es(2026, Tenor::December, None);
        let mut chain = FutChain::new(start, &listing).unwrap();
        chain.advance();
        chain.retreat();
        assert_eq!(chain.contract(), &start);
    }

    #[test]
    fn advance_clears_day() {
        let listing = ListedTenors::quarterly();
        let mut chain = FutChain::new(es(2026, Tenor::March, Some(20)), &listing).unwrap();
        chain.advance();
        assert_eq!(chain.contract().day(), None);
    }

    #[test]
    fn retreat_clears_day() {
        let listing = ListedTenors::quarterly();
        let mut chain = FutChain::new(es(2026, Tenor::June, Some(20)), &listing).unwrap();
        chain.retreat();
        assert_eq!(chain.contract().day(), None);
    }

    #[test]
    fn new_rejects_contract_with_unlisted_tenor() {
        let listing = ListedTenors::quarterly();
        // January is not in the quarterly cycle.
        let err = FutChain::new(es(2026, Tenor::January, None), &listing).unwrap_err();
        assert_eq!(err, FutChainError::ContractTenorNotListed);
    }

    #[test]
    #[should_panic(expected = "year underflow on retreat")]
    fn retreat_panics_at_year_zero() {
        let listing = ListedTenors::quarterly();
        let mut chain = FutChain::new(es(0, Tenor::March, None), &listing).unwrap();
        chain.retreat(); // March year 0 -> December year -1 → underflow
    }

    #[test]
    fn advance_by_zero_is_noop() {
        let listing = ListedTenors::quarterly();
        let start = es(2026, Tenor::June, None);
        let mut chain = FutChain::new(start, &listing).unwrap();
        chain.advance_by(0);
        assert_eq!(chain.contract(), &start);
    }

    #[test]
    fn advance_by_steps_through_year_boundary() {
        let listing = ListedTenors::quarterly();
        // Start at Mar 2026, take 5 steps: Jun, Sep, Dec, Mar+1, Jun+1.
        let mut chain = FutChain::new(es(2026, Tenor::March, None), &listing).unwrap();
        chain.advance_by(5);
        assert_eq!(chain.contract().tenor(), Tenor::June);
        assert_eq!(chain.contract().year(), 2027);
    }

    #[test]
    fn retreat_by_zero_is_noop() {
        let listing = ListedTenors::quarterly();
        let start = es(2026, Tenor::June, None);
        let mut chain = FutChain::new(start, &listing).unwrap();
        chain.retreat_by(0);
        assert_eq!(chain.contract(), &start);
    }

    #[test]
    fn retreat_by_steps_through_year_boundary() {
        let listing = ListedTenors::quarterly();
        // Start at Jun 2026, take 5 steps back: Mar, Dec-1, Sep-1, Jun-1, Mar-1.
        let mut chain = FutChain::new(es(2026, Tenor::June, None), &listing).unwrap();
        chain.retreat_by(5);
        assert_eq!(chain.contract().tenor(), Tenor::March);
        assert_eq!(chain.contract().year(), 2025);
    }

    #[test]
    fn advance_by_wraps_multiple_years() {
        let listing = ListedTenors::quarterly();
        // Mar 2026 + 9 steps = 9/4 = 2 full years, 9%4 = 1 → Jun 2028.
        let mut chain = FutChain::new(es(2026, Tenor::March, None), &listing).unwrap();
        chain.advance_by(9);
        assert_eq!(chain.contract().tenor(), Tenor::June);
        assert_eq!(chain.contract().year(), 2028);
    }

    #[test]
    fn retreat_by_wraps_multiple_years() {
        let listing = ListedTenors::quarterly();
        // Jun 2026 - 9 steps. Each year is 4 steps. 9 = 4+4+1: back through
        // Mar 2026, Dec 2025, Sep 2025, Jun 2025, Mar 2025, Dec 2024, Sep 2024,
        // Jun 2024, Mar 2024 → land on Mar 2024.
        let mut chain = FutChain::new(es(2026, Tenor::June, None), &listing).unwrap();
        chain.retreat_by(9);
        assert_eq!(chain.contract().tenor(), Tenor::March);
        assert_eq!(chain.contract().year(), 2024);
    }

    #[test]
    fn advance_by_listing_len_adds_one_year() {
        let listing = ListedTenors::quarterly();
        let start = es(2026, Tenor::June, None);
        let mut chain = FutChain::new(start, &listing).unwrap();
        chain.advance_by(listing.len());
        assert_eq!(chain.contract().tenor(), start.tenor());
        assert_eq!(chain.contract().year(), start.year() + 1);
    }

    #[test]
    fn retreat_by_listing_len_subtracts_one_year() {
        let listing = ListedTenors::quarterly();
        let start = es(2026, Tenor::June, None);
        let mut chain = FutChain::new(start, &listing).unwrap();
        chain.retreat_by(listing.len());
        assert_eq!(chain.contract().tenor(), start.tenor());
        assert_eq!(chain.contract().year(), start.year() - 1);
    }

    #[test]
    fn advance_by_matches_repeated_advance() {
        let listing = ListedTenors::quarterly();
        let start = es(2026, Tenor::September, None);
        let mut by = FutChain::new(start, &listing).unwrap();
        let mut loop_ = FutChain::new(start, &listing).unwrap();
        by.advance_by(7);
        for _ in 0..7 {
            loop_.advance();
        }
        assert_eq!(by.contract(), loop_.contract());
    }

    #[test]
    #[should_panic(expected = "year overflow on advance")]
    fn advance_panics_at_year_max() {
        let listing = ListedTenors::quarterly();
        let mut chain = FutChain::new(es(u16::MAX, Tenor::December, None), &listing).unwrap();
        chain.advance(); // December year MAX -> March year MAX+1 → overflow
    }
}
