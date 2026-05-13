use std::{collections::HashMap, fmt::Display};

use instrid::prelude::Tenor;

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
    /// Build a listing from a non-empty, duplicate-free set of tenors.
    /// The input is sorted chronologically.
    ///
    /// ```
    /// use futchain::ListedTenors;
    /// use instrid::prelude::Tenor;
    ///
    /// // Quarterly cycle, given in arbitrary order — stored sorted.
    /// let quarterly = ListedTenors::new(vec![
    ///     Tenor::December,
    ///     Tenor::March,
    ///     Tenor::September,
    ///     Tenor::June,
    /// ]).unwrap();
    ///
    /// assert_eq!(quarterly.first(), Tenor::March);
    /// assert_eq!(quarterly.last(), Tenor::December);
    /// assert_eq!(quarterly.len(), 4);
    /// ```
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

    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    pub fn first(&self) -> Tenor {
        self.buffer[0]
    }

    pub fn last(&self) -> Tenor {
        self.buffer[self.buffer.len() - 1]
    }

    pub fn nth(&self, i: usize) -> Option<Tenor> {
        self.buffer.get(i).copied()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_rejects_empty() {
        assert!(matches!(
            ListedTenors::new(vec![]),
            Err(ListedTenorsError::Empty),
        ));
    }

    #[test]
    fn new_rejects_duplicates() {
        let err = ListedTenors::new(vec![Tenor::March, Tenor::March, Tenor::June])
            .expect_err("duplicates should be rejected");
        match err {
            ListedTenorsError::Duplicate(dups) => {
                assert_eq!(dups.get(&Tenor::March), Some(&2));
                assert!(!dups.contains_key(&Tenor::June));
            }
            other => panic!("expected Duplicate, got {other:?}"),
        }
    }
}
