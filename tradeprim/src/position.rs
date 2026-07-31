use std::{cmp::Ordering, fmt::Display, ops::Add};

use crate::quantity::Quantity;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Default, Hash)]
pub enum Position {
    #[default]
    Flat,
    Long(NonZeroQuantity),
    Short(NonZeroQuantity),
}

impl Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Position::Flat => write!(f, "0"),
            Position::Long(quantity) => {
                write!(f, "{}", quantity.qty)
            }
            Position::Short(quantity) => {
                write!(f, "-{}", quantity.qty)
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct PositionOverflow {
    current: Position,
    add: Position,
}

impl PositionOverflow {
    pub fn current(&self) -> Position {
        self.current
    }

    pub fn add(&self) -> Position {
        self.add
    }
}

impl Display for PositionOverflow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "PositionOverflow {{\n\tcurrent: {},\n\tadd: {}\n}}",
            self.current, self.add
        )
    }
}

impl std::error::Error for PositionOverflow {}

impl Add for Position {
    type Output = Result<Position, PositionOverflow>;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Position::Long(a), Position::Short(b)) | (Position::Short(b), Position::Long(a)) => {
                match a.cmp(&b) {
                    Ordering::Greater => {
                        Ok(Position::Long((a.qty - b.qty).unwrap().non_zero().unwrap()))
                    }
                    Ordering::Less => Ok(Position::Short(
                        (b.qty - a.qty).unwrap().non_zero().unwrap(),
                    )),
                    Ordering::Equal => Ok(Position::Flat),
                }
            }
            (Position::Flat, a) | (a, Position::Flat) => Ok(a),
            // S,S || LL
            (Position::Long(a), Position::Long(b)) => Ok(Position::Long(
                (a.qty + b.qty)
                    .ok_or(PositionOverflow {
                        current: self,
                        add: rhs,
                    })?
                    .non_zero()
                    .unwrap(),
            )),
            (Position::Short(a), Position::Short(b)) => Ok(Position::Short(
                (a.qty + b.qty)
                    .ok_or(PositionOverflow {
                        current: self,
                        add: rhs,
                    })?
                    .non_zero()
                    .unwrap(),
            )),
        }
    }
}

// Backs up `Position`
#[derive(Hash, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct NonZeroQuantity {
    qty: Quantity,
}

impl NonZeroQuantity {
    pub fn new(quantity: Quantity) -> Option<Self> {
        match quantity {
            Quantity::ZERO => None,
            a => Some(Self { qty: a }),
        }
    }

    pub fn qty(&self) -> Quantity {
        self.qty
    }
}

#[cfg(test)]
mod tests {
    mod positions {
        use proptest::prelude::*;

        use crate::{
            position::{NonZeroQuantity, Position, PositionOverflow},
            quantity::Quantity,
        };

        /// Underlying Quantity overflow. That can happen only with same sides.
        #[test]
        fn same_side_overflow() {
            let max_pos = Position::Long(Quantity::MAX.non_zero().unwrap());
            let min_pos = Position::Long(Quantity::new(1).unwrap().non_zero().unwrap());
            assert_eq!(
                (max_pos + min_pos),
                Err(PositionOverflow {
                    current: max_pos,
                    add: min_pos
                })
            );

            let max_pos = Position::Short(Quantity::MAX.non_zero().unwrap());
            let min_pos = Position::Short(Quantity::new(1).unwrap().non_zero().unwrap());
            assert_eq!(
                (max_pos + min_pos),
                Err(PositionOverflow {
                    current: max_pos,
                    add: min_pos
                })
            );
        }

        #[test]
        fn different_sides_never_overflow_on_edges() {
            let max_long = Position::Long(Quantity::MAX.non_zero().unwrap());
            let max_short = Position::Short(Quantity::MAX.non_zero().unwrap());
            assert_eq!(max_long + max_short, Ok(Position::Flat));
            let min_short = Position::Short(Quantity::new(1).unwrap().non_zero().unwrap());
            assert_eq!(
                max_long + min_short,
                Ok(Position::Long(
                    Quantity::new(Quantity::MAX.value() - 1)
                        .unwrap()
                        .non_zero()
                        .unwrap()
                ))
            );
        }

        #[test]
        fn zero_is_rejected_by_both_constructors() {
            assert!(NonZeroQuantity::new(Quantity::ZERO).is_none());
            assert!(Quantity::ZERO.non_zero().is_none());
        }

        fn arbitrary_position() -> impl Strategy<Value = Position> {
            // Bounded by `MAX_RAW / 3` so no sum (even when I test associativity) can overflow.
            let qty = (1_u64..Quantity::MAX_RAW / 3)
                .prop_map(|v| Quantity::new(v).unwrap().non_zero().unwrap());
            prop_oneof![
                Just(Position::Flat),
                qty.clone().prop_map(Position::Long),
                qty.prop_map(Position::Short),
            ]
        }

        proptest! {
            #[test]
            fn add_is_commutative(a in arbitrary_position(), b in arbitrary_position()) {
                prop_assert_eq!((a + b).unwrap(), (b + a).unwrap());
            }

            // Associative = order doesn't matter
            #[test]
            fn add_is_associative(
                a in arbitrary_position(),
                b in arbitrary_position(),
                c in arbitrary_position(),
            ) {
                let left = ((a + b).unwrap() + c).unwrap();
                let right = (a + (b + c).unwrap()).unwrap();
                prop_assert_eq!(left, right);
            }

            #[test]
            fn opposite_sides_cancel_exactly(q in 1_u64..Quantity::MAX_RAW) {
                let q = Quantity::new(q).unwrap().non_zero().unwrap();
                prop_assert_eq!(
                    (Position::Long(q) + Position::Short(q)).unwrap(),
                    Position::Flat
                );
            }
        }

        mod preserve_behaviour {
            use crate::{position::Position, quantity::Quantity};

            // --- Helper functions
            fn long(s: &str) -> Position {
                Position::Long(Quantity::from_str_unchecked(s).non_zero().unwrap())
            }

            fn short(s: &str) -> Position {
                Position::Short(Quantity::from_str_unchecked(s).non_zero().unwrap())
            }
            // ---

            #[test]
            fn position_add() {
                assert_eq!((long("1.23") + long("1.23")).unwrap(), long("2.46"));
                assert_eq!((long("1.23") + short("1.23")).unwrap(), Position::Flat);
                assert_eq!((short("1.23") + long("1.23")).unwrap(), Position::Flat);
                assert_eq!((short("1.23") + short("1.23")).unwrap(), short("2.46"));

                // Side flips
                assert_eq!((long("3") + short("5")).unwrap(), short("2"));
                assert_eq!((short("3") + long("5")).unwrap(), long("2"));
            }

            #[test]
            fn position_display() {
                let pos = Position::Short(Quantity::from_str_unchecked("1.23").non_zero().unwrap());
                assert_eq!(format!("{}", pos), "-1.23");
                let pos = Position::Long(Quantity::from_str_unchecked("1.23").non_zero().unwrap());
                assert_eq!(format!("{}", pos), "1.23");
                let pos = Position::Flat;
                assert_eq!(format!("{}", pos), "0");
            }

            #[test]
            fn flat_is_neutral() {
                assert_eq!((Position::Flat + long("1")).unwrap(), long("1"));
                assert_eq!((long("1") + Position::Flat).unwrap(), long("1"));
                assert_eq!((Position::Flat + Position::Flat).unwrap(), Position::Flat);
            }

            #[test]
            fn default_is_flat() {
                assert_eq!(Position::default(), Position::Flat);
            }
        }
    }
}
