#![allow(non_snake_case)]
pub mod ADX;
pub mod DEWMA;
pub mod SignalLineMACD;
pub mod TrendStrength3MA;
pub mod AR;
pub mod ATR;
pub mod ConnorsRSI;
pub mod DI;
pub mod EWMA;
pub mod IBS;
pub mod MACD;
pub mod MFI;
pub mod PR;
pub mod RSI;
pub mod SMA;
pub mod Streak;
pub mod TR;
pub mod WilderADX;
pub mod WilderATR;
pub mod WilderDI;

/* PROBABLY TO USE THIS IN SMA
use std::collections::VecDeque;

/// A VecDeque wrapper that maintains a maximum length by popping front when full.
pub struct BoundedVecDeque<T> {
    deque: VecDeque<T>,
    max_len: usize,
}

impl<T> BoundedVecDeque<T> {
    /// Creates a new BoundedVecDeque with the specified maximum length.
    pub fn new(max_len: usize) -> Self {
        if max_len == 0 {
            panic!("max_len must be greater than 0");
        }

        BoundedVecDeque {
            deque: VecDeque::with_capacity(max_len),
            max_len,
        }
    }

    /// Pushes an element to the back, popping from the front if at max length.
    /// Returns the popped or None.
    pub fn push_back(&mut self, value: T) -> Option<T> {
        let popped = match self.deque.len() >= self.max_len {
            true => Some(self.deque.pop_front().unwrap()),
            false => None,
        };
        self.deque.push_back(value);

        popped
    }

    /// Returns the current number of elements.
    pub fn len(&self) -> usize {
        self.deque.len()
    }

    /// Returns the maximum length.
    pub fn max_len(&self) -> usize {
        self.max_len
    }

    /// Returns the current capacity of the underlying VecDeque.
    pub fn capacity(&self) -> usize {
        self.deque.capacity()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bounded_vec_deque() {
        let mut deque = BoundedVecDeque::new(3);
        deque.push_back(1);
        deque.push_back(2);
        deque.push_back(3);
        assert_eq!(deque.len(), 3);
        assert_eq!(deque.deque, VecDeque::from([1, 2, 3]));

        deque.push_back(4); // Should pop 1
        assert_eq!(deque.len(), 3);
        assert_eq!(deque.deque, VecDeque::from([2, 3, 4]));

        deque.push_back(5); // Should pop 2
        assert_eq!(deque.len(), 3);
        assert_eq!(deque.deque, VecDeque::from([3, 4, 5]));
    }
}

*/
