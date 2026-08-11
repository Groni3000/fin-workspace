use std::collections::HashMap;

use chrono::{DateTime, Datelike, NaiveDate};
use chrono_tz::Tz;
use futchain::{FutChain, eot::EndOfTrading};
use instrid::instruments::{FuturesContract, Instrument};
use oms::fill::Fill;
use tradeprim::{position::Position, price::Price, quantity::Quantity};

use crate::{
    event::{Event, Kind},
    market_data::{Candle, Instrumented, RelevantPrice, Timestamped},
    portfolio::Portfolio,
    strategy::Desired,
    strats_impl::strat_1::config::Config,
};

/// Why the strategy decided to flatten. Emitted with the `exit` event for the trade ledger.
#[derive(Debug, Clone, Copy)]
pub enum ExitReason {
    StopLoss,
    TimeExit,
    EndOfTrading,
    Roll,
}

impl std::fmt::Display for ExitReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

pub struct Strategy<E: EndOfTrading> {
    // --- base
    // todo: config, state
    id: String,
    config: Config<E>,
    desired: HashMap<Instrument, Desired>,
    state: State,
}

#[derive(Default)]
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
    /// Contracts rolled away from, waiting on their closing fill before `desired` drops them.
    settling: Vec<Instrument>,
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
        // The feed carries every contract at once, so the traded one comes from config, not data.
        let eot_date = match config.instrument() {
            Instrument::Futures(contract) => Some(config.eot().calculate(&contract)),
            _ => None,
        };
        let state = State {
            traded_instrument: Some(config.instrument()),
            eot_date,
            ..State::default()
        };
        Self {
            id,
            config,
            desired: HashMap::new(),
            state,
        }
    }

    /// Next listed contract after `current`. The chain is rebuilt per roll — a handful per year.
    fn next_contract(&self, current: FuturesContract) -> FuturesContract {
        let mut chain = FutChain::new(current, self.config.listing())
            .expect("invariant: the traded contract's tenor is listed");
        chain.advance();
        *chain.contract()
    }

    pub fn id(&self) -> &str {
        &self.id
    }

    pub fn desired(&self) -> &HashMap<Instrument, Desired> {
        &self.desired
    }

    pub fn on_event<R>(&mut self, event: &Event<R>, pf: &Portfolio)
    where
        R: Timestamped + Instrumented + Candle,
    {
        match event.kind() {
            Kind::MarketData(md) => self.process_md(md),
            Kind::Ack(_order_id) => {
                // This strategy does not require specific actions of Ack.
            }
            Kind::Reject(_order_id) => {
                // This strategy does not require specific actions of Reject.
            }
            Kind::CancelResponse(_order_id, true) => {
                // This strategy does not require specific actions of CancelResponse.
            }
            Kind::CancelResponse(_order_id, false) => {
                // This strategy does not require specific actions of CancelResponse.
            }
            Kind::FeedError(_err) => {
                // This strategy does not require specific actions of FeedError.
            }
            Kind::Fill(fill) => {
                // This strategy does not require specific actions of Fill.
                self.on_fill(fill, pf);
            }
        }
    }

    /// This is market only strategy. We can "dirty-drop" entries.
    ///
    /// This will substantially increase performance by reducing the number of entries in `desired`.
    fn prune_settled(&mut self, pf: &Portfolio) {
        let mut settling = std::mem::take(&mut self.state.settling);
        settling.retain(|instrument| {
            let done = pf.position(instrument) == &Position::Flat
                && self
                    .desired
                    .get(instrument)
                    .is_none_or(|d| d.position() == Position::Flat && d.orders().is_empty());
            if done {
                self.desired.remove(instrument);
            }
            !done
        });
        self.state.settling = settling;
    }

    fn on_fill(&mut self, _fill: &Fill, pf: &Portfolio) {
        // Fills are the only thing that moves a real position.
        self.prune_settled(pf);

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

    fn entry_condition<R>(&mut self, md_record: &R, exchange_ts: DateTime<Tz>) -> bool
    where
        R: Timestamped + Instrumented + RelevantPrice,
    {
        if self.state.fired_today {
            return false;
        }
        let exchange_time = exchange_ts.time();
        if exchange_time >= self.config.entry_time().0
            && exchange_time < self.config.entry_time().1
            && exchange_ts.weekday() == self.config().day_of_week()
        {
            self.state.fired_today = true;
            *self
                .desired
                .entry(md_record.instrument())
                .or_default()
                .mut_position() =
                Position::Long(Quantity::from_str_unchecked("1").non_zero().unwrap());
            let stop = Price::new(
                md_record.last_price().value() - self.config.stop_loss_price_diff().value(),
            );
            self.state.stop_loss_price = stop;
            tracing::info!(
                instrument = %md_record.instrument(),
                signal_price = %md_record.last_price(),
                stop = %stop.map(|p| p.to_string()).unwrap_or_default(),
                "entry"
            );

            return true;
        }
        false
    }

    fn out_condition<R>(&mut self, md_record: &R, exchange_ts: DateTime<Tz>)
    where
        R: Timestamped + Instrumented + Candle,
    {
        let exchange_time = exchange_ts.time();
        let stop_loss_fired = if let Some(sl_price) = self.state.stop_loss_price {
            md_record.low() <= sl_price
        } else {
            false
        };
        if exchange_time > self.config.out_time() || stop_loss_fired {
            let reason = if stop_loss_fired {
                ExitReason::StopLoss
            } else {
                ExitReason::TimeExit
            };
            if let Some(desired) = self.desired.get_mut(&md_record.instrument()) {
                *desired.mut_position() = Position::Flat;
            }
            tracing::info!(
                instrument = %md_record.instrument(),
                %reason,
                signal_price = %md_record.last_price(),
                "exit"
            );
            self.state.n_trades += 1;
            self.state.stop_loss_price = None;
        }
    }

    /// Roll to the next contract at EOT. Deal with desired of the previous one.
    ///
    /// If there is still an open position - we change its desired state to Flat. We have protective
    /// EoT-offset, so this is pretty much guaranteed to be closed.
    fn roll_condition(&mut self, date: NaiveDate) {
        while self.state.eot_date.is_some_and(|eot| date >= eot) {
            let Some(Instrument::Futures(current)) = self.state.traded_instrument else {
                self.state.eot_date = None;
                return;
            };
            let next = Instrument::Futures(self.next_contract(current));
            let previous = Instrument::Futures(current);

            if let Some(desired) = self.desired.get_mut(&previous)
                && desired.position() != Position::Flat
            {
                *desired.mut_position() = Position::Flat;
                tracing::info!(instrument = %previous, reason = %ExitReason::Roll, "exit");
            }
            self.state.settling.push(previous);
            self.state.stop_loss_price = None;
            self.state.traded_instrument = Some(next);
            self.state.eot_date = match next {
                Instrument::Futures(contract) => Some(self.config.eot().calculate(&contract)),
                _ => None,
            };
            tracing::info!(from = %previous, to = %next, "roll");
        }
    }

    fn process_md<R>(&mut self, md_record: &R)
    where
        R: Timestamped + Instrumented + Candle,
    {
        // The only tz conversion per record: chrono-tz binary-searches transitions on each call.
        let exchange_ts = md_record
            .timestamp()
            .with_timezone(&self.config.exchange_tz());

        let date = exchange_ts.date_naive();
        if self.state.last_known_date != date {
            self.state.fired_today = false;
            self.state.last_known_date = date;
        }

        self.roll_condition(date);
        // Only trade the current contract.
        if self.state.traded_instrument != Some(md_record.instrument()) {
            return;
        }

        let current_position = self
            .desired
            .get(&md_record.instrument())
            .map_or(Position::Flat, Desired::position);

        if current_position == Position::Flat && self.entry_condition(md_record, exchange_ts) {
            // Do not check for exit on the same md_record
            return;
        }
        if current_position != Position::Flat {
            self.out_condition(md_record, exchange_ts);
        }
    }

    pub fn config(&self) -> &Config<E> {
        &self.config
    }

    pub fn state(&self) -> &State {
        &self.state
    }
}
