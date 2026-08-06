use std::collections::HashMap;

use chrono::NaiveDate;
use instrid::instruments::Instrument;
use oms::fill::Fill;
use tradeprim::{position::Position, price::Price, quantity::Quantity};

use crate::{
    event::{Event, Kind},
    formats::{Tagged, frd::FrdCandle},
    market_data::{RelevantPrice, Timestamped},
    strategy::Desired,
    strats_impl::strat_1::config::Config,
};

type MdRecord = Tagged<FrdCandle>;

pub struct Strategy {
    // --- base
    // todo: config, state
    id: String,
    config: Config,
    desired: HashMap<Instrument, Desired>,
    state: State,
}

pub struct State {
    /// If we get stop loss, we will not fire again today.
    fired_today: bool,
    last_known_date: NaiveDate,
    n_trades: u64,
    stop_loss_price: Option<Price>,
}

impl Default for State {
    fn default() -> Self {
        Self {
            fired_today: false,
            last_known_date: NaiveDate::default(),
            n_trades: 0,
            stop_loss_price: None,
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
}

impl Strategy {
    pub fn new(id: String, config: Config) -> Self {
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

    pub fn on_event(&mut self, event: &Event<MdRecord>) {
        let dt = chrono::DateTime::from_timestamp_nanos(event.ts())
            .with_timezone(&self.config.exchange_tz())
            .date_naive();
        if self.state.last_known_date != dt {
            self.state.fired_today = false;
            self.state.last_known_date = dt;
        }
        match event.kind() {
            Kind::MarketData(md) => self.process_md(md),
            Kind::Ack(_order_id) => {}
            Kind::Reject(_order_id) => {}
            Kind::CancelResponse(_order_id, true) => {}
            Kind::CancelResponse(_order_id, false) => {}
            Kind::FeedError(_err) => {}
            Kind::Fill(fill) => {
                self.on_fill(fill);
            }
        }
    }

    fn on_fill(&mut self, _fill: &Fill) {}

    fn entry_condition(&mut self, md_record: &MdRecord) {
        if self.state.fired_today {
            return;
        }
        let exchange_ts = md_record
            .timestamp()
            .with_timezone(&self.config.exchange_tz());
        let exchange_time = exchange_ts.time();
        if exchange_time >= self.config.entry_time().0 && exchange_time < self.config.entry_time().1
        {
            self.state.fired_today = true;
            *self
                .desired
                .entry(self.config.instrument())
                .or_default()
                .mut_position() =
                Position::Long(Quantity::from_str_unchecked("1").non_zero().unwrap());
            self.state.stop_loss_price = Price::new(
                md_record.last_price().value() - self.config.stop_loss_price_diff().value(),
            );
        }
    }

    fn out_condition(&mut self, md_record: &MdRecord) {
        let exchange_ts = md_record
            .timestamp()
            .with_timezone(&self.config.exchange_tz());
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
                .entry(self.config.instrument())
                .or_default()
                .mut_position() = Position::Flat;
            self.state.n_trades += 1;
            self.state.stop_loss_price = None;
        }
    }

    fn process_md(&mut self, md_record: &MdRecord) {
        self.entry_condition(&md_record);
        self.out_condition(&md_record);
    }

    pub fn config(&self) -> &Config {
        &self.config
    }

    pub fn state(&self) -> &State {
        &self.state
    }
}
