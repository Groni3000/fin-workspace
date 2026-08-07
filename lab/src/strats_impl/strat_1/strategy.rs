use std::collections::HashMap;

use chrono::{DateTime, NaiveDate};
use chrono_tz::Tz;
use futchain::eot::EndOfTrading;
use instrid::instruments::Instrument;
use oms::fill::Fill;
use tradeprim::{position::Position, price::Price, quantity::Quantity};

use crate::{
    event::{Event, Kind},
    formats::{Tagged, frd::FrdCandle},
    market_data::{Instrumented, RelevantPrice, Timestamped},
    portfolio::Portfolio,
    strategy::Desired,
    strats_impl::strat_1::config::Config,
};

type MdRecord = Tagged<FrdCandle>;

pub struct Strategy<E: EndOfTrading> {
    // --- base
    // todo: config, state
    id: String,
    config: Config<E>,
    desired: HashMap<Instrument, Desired>,
    state: State,
}

pub struct State {
    /// If we get stop loss, we will not fire again today.
    fired_today: bool,
    last_known_date: NaiveDate,
    n_trades: u64,
    stop_loss_price: Option<Price>,
    /// Contract the feed is currently on. `config.instrument()` is only the chain root.
    traded_instrument: Option<Instrument>,
    /// End of trading for `traded_instrument`, recomputed on every roll.
    eot_date: Option<NaiveDate>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            fired_today: false,
            last_known_date: NaiveDate::default(),
            n_trades: 0,
            stop_loss_price: None,
            traded_instrument: None,
            eot_date: None,
        }
    }
}

impl State {
    pub fn stop_loss_price(&self) -> Option<Price> {
        self.stop_loss_price
    }

    pub fn last_known_date(&self) -> NaiveDate {
        self.last_known_date
    }

    pub fn traded_instrument(&self) -> Option<Instrument> {
        self.traded_instrument
    }

    pub fn eot_date(&self) -> Option<NaiveDate> {
        self.eot_date
    }
}

impl<E: EndOfTrading> Strategy<E> {
    pub fn new(id: String, config: Config<E>) -> Self {
        let desired = HashMap::new();
        let state = State::default();
        Self {
            id,
            config,
            desired,
            state,
        }
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn desired(&self) -> &HashMap<Instrument, Desired> {
        &self.desired
    }

    pub fn on_event(&mut self, event: &Event<MdRecord>, pf: &Portfolio) {
        match event.kind() {
            Kind::MarketData(md) => self.process_md(md),
            Kind::Ack(_order_id) => {
                // This strategy does not require specific actions of Ack.
            }
            Kind::Reject(_order_id) => {
                todo!()
            }
            Kind::CancelResponse(_order_id, true) => {
                todo!()
            }
            Kind::CancelResponse(_order_id, false) => {
                todo!()
            }
            Kind::FeedError(_err) => {
                todo!()
            }
            Kind::Fill(fill) => {
                // This strategy does not require specific actions of Fill.
                self.on_fill(fill, pf);
            }
        }
    }

    fn on_fill(&mut self, _fill: &Fill, _pf: &Portfolio) {
        // // if order is a protective one
        // pf.orders_idx().get(&fill.order_id()).map(|idx| {
        //     let order = &pf.orders()[*idx];
        //     if order.order_type() != &OrderType::Market {
        //         *self
        //             .desired
        //             .entry(fill.instrument())
        //             .or_default()
        //             .mut_position() -= order.as_position();
        //     }
        // });
        // // and then delete from desired orders
    }

    fn entry_condition(&mut self, md_record: &MdRecord, exchange_ts: DateTime<Tz>) {
        if self.state.fired_today {
            return;
        }
        let exchange_time = exchange_ts.time();
        if exchange_time >= self.config.entry_time().0 && exchange_time < self.config.entry_time().1
        {
            self.state.fired_today = true;
            *self
                .desired
                .entry(md_record.instrument())
                .or_default()
                .mut_position() =
                Position::Long(Quantity::from_str_unchecked("1").non_zero().unwrap());
            self.state.stop_loss_price = Price::new(
                md_record.last_price().value() - self.config.stop_loss_price_diff().value(),
            );
        }
    }

    fn out_condition(&mut self, md_record: &MdRecord, exchange_ts: DateTime<Tz>) {
        let exchange_time = exchange_ts.time();
        let current_price = md_record.last_price();
        let stop_loss_fired = if let Some(sl_price) = self.state.stop_loss_price {
            current_price <= sl_price
        } else {
            false
        };
        if exchange_time > self.config.out_time() || stop_loss_fired {
            *self
                .desired
                .entry(md_record.instrument())
                .or_default()
                .mut_position() = Position::Flat;
            self.state.n_trades += 1;
            self.state.stop_loss_price = None;
        }
    }

    /// All desired positions are flatten if we roll.
    ///
    /// For now it changes nothing:
    /// we roll instrument and .entry/out_condition simply don't touch it.
    fn roll_condition(&mut self, md_record: &MdRecord) {
        let current = md_record.instrument();
        if self.state.traded_instrument == Some(current) {
            return;
        }
        if let Some(previous) = self.state.traded_instrument {
            *self.desired.entry(previous).or_default().mut_position() = Position::Flat;
            self.state.stop_loss_price = None;
            tracing::info!(from = %previous, to = %current, "roll");
        }

        self.state.traded_instrument = Some(current);
        self.state.eot_date = match current {
            Instrument::Futures(contract) => Some(self.config.eot().calculate(&contract)),
            _ => None,
        };
    }

    /// Invariant: `eot < real eot => md still goes`
    ///
    /// When we hit eot - flat position.
    ///
    /// Returns `true` when the contract is done, so entry/out are skipped.
    fn eot_condition(&mut self, md_record: &MdRecord, date: NaiveDate) -> bool {
        let Some(eot) = self.state.eot_date else {
            return false;
        };
        if date < eot {
            return false;
        }

        let instrument = md_record.instrument();
        let entry = self.desired.entry(instrument).or_default();
        if entry.position() != Position::Flat {
            tracing::info!(instrument = %instrument, %eot, "end of trading: flatten");
            *entry.mut_position() = Position::Flat;
        }
        self.state.stop_loss_price = None;
        true
    }

    fn process_md(&mut self, md_record: &MdRecord) {
        // The only tz conversion per record: chrono-tz binary-searches transitions on each call.
        let exchange_ts = md_record
            .timestamp()
            .with_timezone(&self.config.exchange_tz());

        let date = exchange_ts.date_naive();
        if self.state.last_known_date != date {
            self.state.fired_today = false;
            self.state.last_known_date = date;
        }

        self.roll_condition(md_record);
        if self.eot_condition(md_record, date) {
            return;
        }
        self.entry_condition(md_record, exchange_ts);
        self.out_condition(md_record, exchange_ts);
    }

    pub fn config(&self) -> &Config<E> {
        &self.config
    }

    pub fn state(&self) -> &State {
        &self.state
    }
}
