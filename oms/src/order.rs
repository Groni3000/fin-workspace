use std::{fmt::Display, hash::Hash, marker::PhantomData};

use chrono::{DateTime, NaiveDate, Utc};
use instrid::instruments::Instrument;
use tradeprim::{
    Side,
    position::{NonZeroQuantity, Position},
    price::Price,
    quantity::Quantity,
};
use uuid::Uuid;

use crate::{OrderId, fill::Fill};

/// An internal representation of Order.
///
/// Have 3 different states:
///     - **New** - created by strategy, yet not delivered to OrderMS
///     - **Working** - delivered to OMS, in process of execution: may be not acknowledged yet or just resting or partially filled
///     - **Terminated** - Rejected/Cancelled/Filled - fully executed or terminated
///
/// State `New` is `Copy`, we need to have a copy in both Strategy and OMS/Portfolio scopes.
/// Can be transformed into both `Working` (delivered to OMS) and `Terminated` (did no survive RiskMS) states.
///
/// States `Working` and `Terminated` are **not** `Copy`.
/// The only transformations allowed are: `New -> Working|Terminated(RiskReject)`, `Working -> Terminated`.
#[derive(Debug, Clone, Copy)]
pub struct Order<S> {
    order_id: OrderId,
    instrument: Instrument,
    order_type: OrderType,
    time_in_force: TimeInForce,
    side: Side,
    quantity: NonZeroQuantity,
    state: S,
}

//--- States ---
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct New;
#[derive(Debug, PartialEq, Eq)]
pub struct Working {
    leaves: Quantity,
}
#[derive(Debug, PartialEq, Eq)]
pub struct Terminated {
    leaves: Quantity,
    reason: TerminationReason,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TerminationReason {
    Cancel,
    Filled,
    Reject,
    RiskReject,
    /// Filled beyond the requested quantity. Nothing left to fill, so the order terminates.
    Overfilled,
}

//--- States imls ---
impl Working {
    fn new(leaves: Quantity) -> Self {
        Self { leaves }
    }

    pub fn leaves(&self) -> Quantity {
        self.leaves
    }
}

impl Terminated {
    fn new(leaves: Quantity, reason: TerminationReason) -> Self {
        Self { leaves, reason }
    }

    pub fn leaves(&self) -> Quantity {
        self.leaves
    }

    pub fn reason(&self) -> TerminationReason {
        self.reason
    }
}
// --- States end ---

// --- Order generic methods ---
impl<T> Order<T> {
    pub fn order_id(&self) -> OrderId {
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

    pub fn state(&self) -> &T {
        &self.state
    }

    fn set_state<S>(self, state: S) -> Order<S> {
        Order {
            order_id: self.order_id,
            instrument: self.instrument,
            order_type: self.order_type,
            time_in_force: self.time_in_force,
            side: self.side,
            quantity: self.quantity,
            state,
        }
    }
}

impl<T> PartialEq for Order<T> {
    fn eq(&self, other: &Self) -> bool {
        self.order_id == other.order_id
    }
}

impl<T> Eq for Order<T> {}

impl<T> Hash for Order<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.order_id.hash(state);
    }
}

// --- Concrete orders
impl Order<New> {
    fn new(
        instrument: Instrument,
        order_type: OrderType,
        time_in_force: TimeInForce,
        side: Side,
        quantity: NonZeroQuantity,
    ) -> Self {
        Self {
            order_id: OrderId(Uuid::now_v7()),
            instrument,
            order_type,
            time_in_force,
            side,
            quantity,
            state: New,
        }
    }

    pub fn into_working(self) -> Order<Working> {
        self.set_state(Working::new(self.quantity().qty()))
    }

    pub fn risk_reject(self) -> Order<Terminated> {
        self.set_state(Terminated {
            leaves: self.quantity().qty(),
            reason: TerminationReason::RiskReject,
        })
    }
}

impl Order<Working> {
    /// Apply a Fill. Consumes `self`. Emits `FillOutcome` states in which `self` is moved.
    pub fn apply_fill(mut self, fill: &Fill) -> FillOutcome {
        // Check for overfill
        self.state.leaves = match self.state.leaves - fill.quantity() {
            Some(a) => a,
            None => {
                // Overfilled: nothing can fill anymore, so leaves is ZERO, same as `Filled`.
                let excess = (fill.quantity().qty() - self.state.leaves)
                    .and_then(|q| q.non_zero())
                    .expect("overfill implies fill quantity exceeds leaves");
                return FillOutcome::Overfill(
                    self.set_state(Terminated::new(
                        Quantity::ZERO,
                        TerminationReason::Overfilled,
                    )),
                    excess,
                );
            }
        };
        // Check if filled
        match self.state.leaves {
            Quantity::ZERO => FillOutcome::Filled(
                self.set_state(Terminated::new(Quantity::ZERO, TerminationReason::Filled)),
            ),
            _ => FillOutcome::Partial(self),
        }
    }

    pub fn into_cancelled(self) -> Order<Terminated> {
        let leaves_qty = self.state().leaves;
        self.set_state(Terminated {
            leaves: leaves_qty,
            reason: TerminationReason::Cancel,
        })
    }

    pub fn into_rejected(self) -> Order<Terminated> {
        let leaves_qty = self.state().leaves;
        self.set_state(Terminated {
            leaves: leaves_qty,
            reason: TerminationReason::Reject,
        })
    }
}

impl Order<Terminated> {
    /// Terminated order can be expressed as a position.
    ///
    /// Rejects are treated as flat positions.
    pub fn as_position(&self) -> Position {
        match self.state.reason() {
            TerminationReason::Reject | TerminationReason::RiskReject => {
                return Position::Flat;
            }
            TerminationReason::Filled
            | TerminationReason::Cancel
            | TerminationReason::Overfilled => {}
        }
        // Cancels can be partially filled.
        let qty = (self.quantity().qty() - self.state().leaves())
            .expect("Qty >= LeavesQty, Sub should never overflow");
        if qty == Quantity::ZERO {
            return Position::Flat;
        }
        match self.side() {
            Side::Buy => Position::Long(NonZeroQuantity::new_unchecked(qty)),
            Side::Sell => Position::Short(NonZeroQuantity::new_unchecked(qty)),
        }
    }
}

// ---

/// Fill outcome report. Overfill carries the terminated order paired with the excess quantity.
#[derive(Debug)]
pub enum FillOutcome {
    Filled(Order<Terminated>),
    Partial(Order<Working>),
    Overfill(Order<Terminated>, NonZeroQuantity),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Ready;
#[derive(Debug, PartialEq, Eq)]
pub struct NotReady;

#[derive(Debug, PartialEq, Eq)]
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
    pub fn build(self) -> Order<New> {
        Order::<New>::new(
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
            Currency::usd(),
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
            TimeInForce::GoodTillDatetime(DateTime::from_timestamp_nanos(
                1_662_921_288_000_000_000,
            )),
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

    mod transitions {
        use chrono::DateTime;
        use tradeprim::{Side, price::Price, quantity::Quantity};

        use crate::{
            fill::Fill,
            order::{
                FillOutcome, New, Order, OrderBuilder, Terminated, TerminationReason, Working,
                tests::spy,
            },
        };

        // Strategy emits non-mutable orders
        fn spy_new_order() -> Order<New> {
            OrderBuilder::new(spy(), Side::Buy, Quantity::ONE.non_zero().unwrap())
                .verify()
                .unwrap()
                .build()
        }

        fn spy_new_order_of(quantity: Quantity) -> Order<New> {
            OrderBuilder::new(spy(), Side::Buy, quantity.non_zero().unwrap())
                .verify()
                .unwrap()
                .build()
        }

        fn fill_for(order: &Order<Working>, quantity: Quantity) -> Fill {
            Fill::new(
                order.order_id(),
                DateTime::from_timestamp_nanos(1_662_921_288_000_000_000),
                order.instrument(),
                order.side(),
                quantity.non_zero().unwrap(),
                Price::from_str_unchecked("753.23"),
            )
        }

        /// Test pipeline:
        ///
        /// `New -> Working -> Partially filled (x3) -> Filled`
        #[test]
        fn working_into_filled() {
            let total = Quantity::from_str_unchecked("100");
            let strategy_order = spy_new_order_of(total);
            // OMS takes them and converts them into mutable orders
            let mut oms_order = strategy_order.into_working();
            let mut filled = Quantity::ZERO;

            for step in ["10", "20", "25"] {
                let step = Quantity::from_str_unchecked(step);
                let fill = fill_for(&oms_order, step);

                oms_order = match oms_order.apply_fill(&fill) {
                    FillOutcome::Partial(order) => order,
                    other => panic!("expected Partial, got {other:?}"),
                };
                filled = (filled + step).expect("quantity overflow");

                assert_eq!(
                    (total - oms_order.state().leaves()).expect("leaves exceeded quantity"),
                    filled,
                    "after {filled:?} of {total:?} filled"
                );
            }

            let last = fill_for(&oms_order, oms_order.state().leaves());
            match oms_order.apply_fill(&last) {
                FillOutcome::Filled(order) => assert_eq!(
                    order.state(),
                    &Terminated::new(Quantity::ZERO, TerminationReason::Filled)
                ),
                other => panic!("expected Filled, got {other:?}"),
            }
        }

        /// An overfill terminates the order: it can never fill again, and the excess is reported.
        #[test]
        fn working_into_overfilled() {
            let total = Quantity::from_str_unchecked("100");
            let oms_order = spy_new_order_of(total).into_working();
            let overfill = fill_for(&oms_order, Quantity::from_str_unchecked("130"));
            match oms_order.apply_fill(&overfill) {
                FillOutcome::Overfill(order, excess) => {
                    assert_eq!(
                        order.state(),
                        &Terminated::new(Quantity::ZERO, TerminationReason::Overfilled)
                    );
                    assert_eq!(excess.qty(), Quantity::from_str_unchecked("30"));
                }
                other => panic!("expected Overfill, got {other:?}"),
            }
        }

        mod preserve_behaviour {
            use std::{assert_matches, time::SystemTime};

            use chrono::DateTime;
            use tradeprim::{price::Price, quantity::Quantity};

            use crate::{
                fill::Fill,
                order::{
                    FillOutcome, Terminated, TerminationReason, Working,
                    tests::transitions::spy_new_order,
                },
            };

            #[test]
            fn new_into_working() {
                let strategy_order = spy_new_order();
                let oms_order = strategy_order.into_working();
                assert_eq!(strategy_order.order_id(), oms_order.order_id());
                assert_eq!(
                    oms_order.state(),
                    &Working::new(strategy_order.quantity().qty())
                );
            }

            #[test]
            fn new_into_terminated() {
                let strategy_order = spy_new_order();
                let terminated_order = strategy_order.risk_reject();
                assert_eq!(strategy_order.order_id(), terminated_order.order_id());
                assert_eq!(
                    terminated_order.state(),
                    &Terminated {
                        // New could not be Partially filled
                        leaves: strategy_order.quantity().qty(),
                        reason: TerminationReason::RiskReject
                    }
                );
            }

            #[test]
            fn working_into_non_fill_terminated() {
                // No partial filled
                let strategy_order = spy_new_order();
                let terminated_order = strategy_order.into_working().into_cancelled();
                assert_eq!(
                    terminated_order.state(),
                    &Terminated {
                        leaves: strategy_order.quantity().qty(),
                        reason: TerminationReason::Cancel
                    }
                );
                // With partial filled
                let strategy_order = spy_new_order();
                let oms_order = strategy_order.into_working();
                let timestamp = DateTime::from_timestamp_secs(
                    SystemTime::now()
                        .duration_since(SystemTime::UNIX_EPOCH)
                        .unwrap()
                        .as_secs() as i64,
                )
                .unwrap();
                let fill = Fill::new(
                    // Partial fill
                    oms_order.order_id(),
                    timestamp,
                    oms_order.instrument(),
                    oms_order.side(),
                    // qty = 0.5
                    Quantity::new(Quantity::SCALE / 2)
                        .unwrap()
                        .non_zero()
                        .unwrap(),
                    Price::from_str_unchecked("753.23"),
                );
                let fill_outcome = oms_order.apply_fill(&fill);
                assert_matches!(fill_outcome, FillOutcome::Partial(_));
                let (oms_order, leaves_qty) = match fill_outcome {
                    FillOutcome::Partial(partial) => {
                        let leaves_qty = partial.state().leaves();
                        (partial, leaves_qty)
                    }
                    _ => unreachable!(),
                };
                let terminated_order = oms_order.into_cancelled();
                assert_eq!(
                    terminated_order.state(),
                    &Terminated {
                        leaves: leaves_qty,
                        reason: TerminationReason::Cancel
                    }
                );
            }

            #[test]
            fn working_into_rejected() {
                let strategy_order = spy_new_order();
                let terminated_order = strategy_order.into_working().into_rejected();
                assert_eq!(strategy_order.order_id(), terminated_order.order_id());
                assert_eq!(
                    terminated_order.state(),
                    &Terminated {
                        leaves: strategy_order.quantity().qty(),
                        reason: TerminationReason::Reject
                    }
                );
            }
        }
    }
}
