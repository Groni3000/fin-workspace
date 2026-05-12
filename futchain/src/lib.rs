use std::{collections::HashMap, fmt::Display};

use instrid::prelude::{FuturesContract, Tenor};

#[derive(Debug)]
pub struct FutChain<'a> {
    cursor: FuturesContract,
    listing: &'a ListedTenors,
}

#[derive(Debug)]
pub struct ListedTenors {
    buffer: Vec<Tenor>,
}

impl Display for ListedTenors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.buffer
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

#[derive(Debug)]
pub enum ListedTenorsError {
    Empty,
    Duplicate(HashMap<Tenor, usize>),
}

impl ListedTenors {
    pub fn new(tenors: Vec<Tenor>) -> Result<Self, ListedTenorsError> {
        // Not empty
        if tenors.is_empty() {
            return Err(ListedTenorsError::Empty);
        }

        // Check uniqueness
        let mut seen: HashMap<Tenor, usize> = HashMap::new();

        for tenor in &tenors {
            seen.entry(*tenor)
                .and_modify(|count| *count += 1)
                .or_insert(1);
        }

        let dups = seen
            .into_iter()
            .filter(|(_tenor, count)| count > &1)
            .collect::<HashMap<Tenor, usize>>();

        if !dups.is_empty() {
            return Err(ListedTenorsError::Duplicate(dups));
        }

        // Sort tenors
        let mut tenors = tenors;
        tenors.sort();

        Ok(Self { buffer: tenors })
    }

    pub fn contains(&self, tenor: Tenor) -> bool {
        self.buffer.contains(&tenor)
    }

    pub fn find(&self, tenor: &Tenor) -> Option<usize> {
        self.buffer.iter().position(|t| t == tenor)
    }
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
}
