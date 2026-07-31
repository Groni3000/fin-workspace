use std::{fmt::Display, marker::PhantomData};

use chrono::{DateTime, NaiveDate, Utc};
use instrid::instruments::Instrument;
use tradeprim::{Side, position::NonZeroQuantity, price::Price};
use uuid::Uuid;

#[derive(Debug)]
pub struct Order {
    order_id: Uuid,
    instrument: Instrument,
    order_type: OrderType,
    time_in_force: TimeInForce,
    side: Side,
    quantity: NonZeroQuantity,
}

impl Order {
    fn new(
        instrument: Instrument,
        order_type: OrderType,
        time_in_force: TimeInForce,
        side: Side,
        quantity: NonZeroQuantity,
    ) -> Self {
        Self {
            order_id: Uuid::now_v7(),
            instrument,
            order_type,
            time_in_force,
            side,
            quantity,
        }
    }

    pub fn order_id(&self) -> Uuid {
        self.order_id
    }

    pub fn instrument(&self) -> Instrument {
        self.instrument
    }

    pub fn order_type(&self) -> &OrderType {
        &self.order_type
    }

    pub fn time_in_force(&self) -> &TimeInForce {
        &self.time_in_force
    }

    pub fn side(&self) -> Side {
        self.side
    }

    pub fn quantity(&self) -> NonZeroQuantity {
        self.quantity
    }
}

impl PartialEq for Order {
    fn eq(&self, other: &Self) -> bool {
        self.order_id == other.order_id
    }
}

impl Eq for Order {}

#[derive(Debug, PartialEq, Eq)]
pub struct Ready;
#[derive(Debug, PartialEq, Eq)]
pub struct NotReady;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct OrderBuilder<T> {
    instrument: Instrument,
    order_type: Option<OrderType>,
    time_in_force: Option<TimeInForce>,
    side: Side,
    quantity: NonZeroQuantity,
    _build_status: PhantomData<fn() -> T>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum OrderBuilderError {
    IncompatibleOrderTypeAndTif(OrderType, TimeInForce),
}

impl Display for OrderBuilderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OrderBuilderError::IncompatibleOrderTypeAndTif(t, k) => {
                write!(f, "Incompatible: {} and {}", t, k)
            }
        }
    }
}

impl std::error::Error for OrderBuilderError {}

impl OrderBuilder<NotReady> {
    pub fn new(instrument: Instrument, side: Side, quantity: NonZeroQuantity) -> Self {
        OrderBuilder {
            instrument,
            order_type: None,
            time_in_force: None,
            side,
            quantity,
            _build_status: PhantomData,
        }
    }

    pub fn with_order_type(mut self, order_type: OrderType) -> Self {
        self.order_type = Some(order_type);
        self
    }

    pub fn with_time_in_force(mut self, time_in_force: TimeInForce) -> Self {
        self.time_in_force = Some(time_in_force);
        self
    }

    pub fn verify(self) -> Result<OrderBuilder<Ready>, OrderBuilderError> {
        let order_type = self.order_type.unwrap_or_default();
        let time_in_force = self.time_in_force.unwrap_or_default();
        // No wildcard to maintain exhaustiveness
        match (order_type, time_in_force) {
            // Market + Day, FOK, IOC = Ok
            (
                OrderType::Market,
                TimeInForce::Day | TimeInForce::FillOrKill | TimeInForce::ImmediateOrCancel,
            ) => {}
            // OT: needs price(s) + Day, GootTill* = Ok
            (
                OrderType::Limit(_) | OrderType::Stop(_) | OrderType::StopLimit(_, _),
                TimeInForce::Day
                | TimeInForce::GoodTillCancel
                | TimeInForce::GoodTillDate(_)
                | TimeInForce::GoodTillDatetime(_),
            ) => {}
            // OT: needs price(s) + FOK, IOC = Err
            (
                OrderType::Limit(_) | OrderType::Stop(_) | OrderType::StopLimit(_, _),
                TimeInForce::FillOrKill | TimeInForce::ImmediateOrCancel,
            ) => {
                return Err(OrderBuilderError::IncompatibleOrderTypeAndTif(
                    order_type,
                    time_in_force,
                ));
            }
            // Market + GoodTill* = Err
            (
                OrderType::Market,
                TimeInForce::GoodTillCancel
                | TimeInForce::GoodTillDate(_)
                | TimeInForce::GoodTillDatetime(_),
            ) => {
                return Err(OrderBuilderError::IncompatibleOrderTypeAndTif(
                    order_type,
                    time_in_force,
                ));
            }
        };

        Ok(OrderBuilder::<Ready> {
            instrument: self.instrument,
            order_type: self.order_type,
            time_in_force: self.time_in_force,
            side: self.side,
            quantity: self.quantity,
            _build_status: PhantomData,
        })
    }
}

impl OrderBuilder<Ready> {
    pub fn build(self) -> Order {
        Order::new(
            self.instrument,
            self.order_type.unwrap_or_default(),
            self.time_in_force.unwrap_or_default(),
            self.side,
            self.quantity,
        )
    }
}

/// Represents the type of order to place.
#[derive(Debug, PartialEq, Eq, Default, Clone, Copy)]
pub enum OrderType {
    #[default]
    Market,
    Stop(Price),
    Limit(Price),
    // A tuple of `(stop_price, limit_price)`
    StopLimit(Price, Price),
}

impl Display for OrderType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// Represents how long an order should be active.
#[derive(Debug, PartialEq, Eq, Default, Clone, Copy)]
pub enum TimeInForce {
    #[default]
    Day,
    GoodTillCancel,
    FillOrKill,
    ImmediateOrCancel,
    GoodTillDate(NaiveDate),
    GoodTillDatetime(DateTime<Utc>),
}

impl Display for TimeInForce {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[cfg(test)]
mod tests {
    use chrono::{DateTime, NaiveDate};
    use instrid::prelude::{Asset, AssetClass, Instrument, Mic, Stock};
    use tradeprim::{prelude::Currency, price::Price};

    use crate::order::{OrderType, TimeInForce};

    fn spy() -> Instrument {
        Instrument::Stock(Stock::new(
            Asset::new("SPY", AssetClass::Equity).unwrap(),
            Asset::new("USD", AssetClass::Currency).unwrap(),
            Mic::arcx(),
            Currency::usd().into(),
        ))
    }

    /// Returns all order types with exhaustive pattern matching
    ///
    /// That way I won't forget to add tests to new variants
    fn all_order_types() -> [OrderType; 4] {
        let all = [
            OrderType::Market,
            OrderType::Limit(Price::ONE),
            OrderType::Stop(Price::ONE),
            OrderType::StopLimit(Price::ONE, Price::ONE),
        ];

        all.iter().for_each(|order_type| match order_type {
            OrderType::Market => {}
            OrderType::Limit(_) => {}
            OrderType::Stop(_) => {}
            OrderType::StopLimit(_, _) => {}
        });

        all
    }

    /// Returns all time in force with exhaustive pattern matching
    ///
    /// That way I won't forget to add tests to new variants
    fn all_tifs() -> [TimeInForce; 6] {
        let all = [
            TimeInForce::Day,
            TimeInForce::GoodTillCancel,
            TimeInForce::FillOrKill,
            TimeInForce::ImmediateOrCancel,
            TimeInForce::GoodTillDate(NaiveDate::from_yo_opt(2000, 57).expect("invalid date")),
            TimeInForce::GoodTillDatetime(DateTime::from_timestamp_nanos(1662921288_000_000_000)),
        ];

        all.iter().for_each(|order_type| match order_type {
            TimeInForce::Day => {}
            TimeInForce::GoodTillCancel => {}
            TimeInForce::FillOrKill => {}
            TimeInForce::ImmediateOrCancel => {}
            TimeInForce::GoodTillDate(_) => {}
            TimeInForce::GoodTillDatetime(_) => {}
        });

        all
    }

    mod builder {
        /// Verify method is very important. It makes a correct order that is ready to send
        /// to executor.
        ///
        /// Every check is performed here:
        ///     - Types compatibility
        ///     - Price/Quantity on ticks by spec
        mod verify {
            use tradeprim::{Side, quantity::Quantity};

            use crate::order::{
                OrderBuilder, OrderType, TimeInForce,
                tests::{all_order_types, all_tifs, spy},
            };
            #[test]
            fn compatible_order_types_and_tifs() {
                // Market is compatible with every Tif that is not `till`
                // Exhaustive filter
                let tifs: [TimeInForce; 3] = all_tifs()
                    .into_iter()
                    .filter(|tif| match tif {
                        // I want to check
                        TimeInForce::Day
                        | TimeInForce::FillOrKill
                        | TimeInForce::ImmediateOrCancel => true,
                        // DON'T check
                        TimeInForce::GoodTillCancel
                        | TimeInForce::GoodTillDate(_)
                        | TimeInForce::GoodTillDatetime(_) => false,
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                for tif in tifs {
                    assert!(
                        OrderBuilder::new(spy(), Side::Sell, Quantity::ONE.non_zero().unwrap())
                            .with_order_type(OrderType::Market)
                            .with_time_in_force(tif)
                            .verify()
                            .is_ok(),
                        "{tif} should be compatible with Market order"
                    );
                }

                // OrderTypes that require price(s) are compatible with every Tif that is `till`
                // Exhaustive filter
                let order_types: [OrderType; 3] = all_order_types()
                    .into_iter()
                    .filter(|order_type| match order_type {
                        OrderType::Market => false,
                        OrderType::Limit(_) | OrderType::Stop(_) | OrderType::StopLimit(_, _) => {
                            true
                        }
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let tifs: [TimeInForce; 4] = all_tifs()
                    .into_iter()
                    .filter(|tif| match tif {
                        // DON'T check
                        TimeInForce::FillOrKill | TimeInForce::ImmediateOrCancel => false,
                        // I want to check
                        TimeInForce::GoodTillCancel
                        | TimeInForce::Day
                        | TimeInForce::GoodTillDate(_)
                        | TimeInForce::GoodTillDatetime(_) => true,
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                for order_type in order_types {
                    for tif in tifs {
                        let result =
                            OrderBuilder::new(spy(), Side::Buy, Quantity::ONE.non_zero().unwrap())
                                .with_order_type(order_type)
                                .with_time_in_force(tif)
                                .verify();
                        assert!(
                            result.is_ok(),
                            "{order_type} + {tif} should not be rejected"
                        );
                    }
                }
            }

            #[test]
            fn not_compatible_order_types_and_tifs() {
                // Market is compatible with every Tif that is not `till`
                // Exhaustive filter
                let tifs: [TimeInForce; 3] = all_tifs()
                    .into_iter()
                    .filter(|tif| match tif {
                        // DON'T check
                        TimeInForce::Day
                        | TimeInForce::FillOrKill
                        | TimeInForce::ImmediateOrCancel => false,
                        // I want to check
                        TimeInForce::GoodTillCancel
                        | TimeInForce::GoodTillDate(_)
                        | TimeInForce::GoodTillDatetime(_) => true,
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                for tif in tifs {
                    assert!(
                        OrderBuilder::new(spy(), Side::Sell, Quantity::ONE.non_zero().unwrap())
                            .with_order_type(OrderType::Market)
                            .with_time_in_force(tif)
                            .verify()
                            .is_err(),
                        "{tif} should not be compatible with Market order"
                    );
                }

                // OrderTypes that require price(s) are compatible with every Tif that is `till`
                // Exhaustive filter
                let order_types: [OrderType; 3] = all_order_types()
                    .into_iter()
                    .filter(|order_type| match order_type {
                        OrderType::Market => false,
                        OrderType::Limit(_) | OrderType::Stop(_) | OrderType::StopLimit(_, _) => {
                            true
                        }
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();
                let tifs: [TimeInForce; 2] = all_tifs()
                    .into_iter()
                    .filter(|tif| match tif {
                        // I want to check
                        TimeInForce::FillOrKill | TimeInForce::ImmediateOrCancel => true,
                        // DON'T check
                        TimeInForce::GoodTillCancel
                        | TimeInForce::Day
                        | TimeInForce::GoodTillDate(_)
                        | TimeInForce::GoodTillDatetime(_) => false,
                    })
                    .collect::<Vec<_>>()
                    .try_into()
                    .unwrap();

                for order_type in order_types {
                    for tif in tifs {
                        let result =
                            OrderBuilder::new(spy(), Side::Buy, Quantity::ONE.non_zero().unwrap())
                                .with_order_type(order_type)
                                .with_time_in_force(tif)
                                .verify();
                        assert!(result.is_err(), "{order_type} + {tif} should be rejected");
                    }
                }
            }
        }

        mod preserve_behavior {

            use tradeprim::{Side, quantity::Quantity};

            use crate::order::{OrderBuilder, OrderType, TimeInForce, tests::spy};

            /// deafult is:
            ///  - OrderType::Market
            ///  - Tif::Day
            #[test]
            fn default_build() {
                let order_builder = OrderBuilder::new(
                    spy(),
                    Side::Buy,
                    Quantity::from_str_unchecked("12").non_zero().unwrap(),
                )
                .verify();
                assert!(order_builder.is_ok());
                let order = order_builder.unwrap().build();

                // Orders are compared by id only, so I check eq by field
                assert_eq!(order.instrument(), spy());
                assert_eq!(order.order_type(), &OrderType::Market);
                assert_eq!(order.time_in_force(), &TimeInForce::Day);
                assert_eq!(order.side(), Side::Buy);
                assert_eq!(
                    order.quantity(),
                    Quantity::from_str_unchecked("12").non_zero().unwrap()
                );
            }

            /// Orders are equal by id only
            #[test]
            fn orders_eq_by_id_only() {
                let order_1 = OrderBuilder::new(
                    spy(),
                    Side::Buy,
                    Quantity::from_str_unchecked("1").non_zero().unwrap(),
                )
                .verify()
                .unwrap()
                .build();
                let order_2 = OrderBuilder::new(
                    spy(),
                    Side::Buy,
                    Quantity::from_str_unchecked("1").non_zero().unwrap(),
                )
                .verify()
                .unwrap()
                .build();
                assert_ne!(order_1, order_2);
            }
        }
    }
}
