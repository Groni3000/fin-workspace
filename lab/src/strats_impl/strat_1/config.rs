use futchain::{
    ListedTenors,
    eot::{DateOffset, EndOfTrading, LastNthBDayOfPrevMonth},
};
use instrid::{
    asset::{Asset, AssetClass},
    instruments::{FuturesContract, Instrument},
    mic::Mic,
    spec::Specification,
    tenor::Tenor,
};
use jiff::{
    SignedDuration,
    civil::{Time, Weekday, time},
    tz::TimeZone,
};
use tradeprim::{
    currency::Currency,
    price::Price,
    quantity::{QtyStep, Quantity},
};

#[derive(Debug)]
pub struct Config<E: EndOfTrading> {
    instrument: Instrument,
    spec: Specification,
    listing: ListedTenors,
    eot: E,
    day_of_week: Weekday,
    exchange_tz: TimeZone,
    /// (start, end)
    entry_time: (Time, Time),
    out_time: Time,
    stop_loss_price_diff: Price,
}

impl<E: EndOfTrading> Config<E> {
    #[expect(
        clippy::too_many_arguments,
        reason = "It's a dirty first try, I add and remove arguments, it would be overkill to design something more"
    )]
    pub fn new(
        instrument: Instrument,
        spec: Specification,
        listing: ListedTenors,
        eot: E,
        day_of_week: Weekday,
        exchange_tz: TimeZone,
        entry_time: Time,
        entry_window_duration: SignedDuration,
        out_time: Time,
        stop_loss_price_diff: Price,
    ) -> Self {
        let entry_time_end = entry_time + entry_window_duration;
        if out_time < entry_time {
            panic!("out_time must be after entry_time");
        }
        Self {
            instrument,
            spec,
            listing,
            eot,
            day_of_week,
            exchange_tz,
            entry_time: (entry_time, entry_time_end),
            out_time,
            stop_loss_price_diff,
        }
    }

    pub fn exchange_tz(&self) -> &TimeZone {
        &self.exchange_tz
    }

    pub fn entry_time(&self) -> (Time, Time) {
        self.entry_time
    }

    pub fn out_time(&self) -> Time {
        self.out_time
    }

    pub fn stop_loss_price_diff(&self) -> Price {
        self.stop_loss_price_diff
    }

    pub fn instrument(&self) -> Instrument {
        self.instrument
    }

    pub fn day_of_week(&self) -> Weekday {
        self.day_of_week
    }

    pub fn spec(&self) -> Specification {
        self.spec
    }

    pub fn eot(&self) -> &E {
        &self.eot
    }

    pub fn listing(&self) -> &ListedTenors {
        &self.listing
    }
}

/// Defaults describe RB: the contract, its spec, and its termination rule.
impl Default for Config<LastNthBDayOfPrevMonth> {
    fn default() -> Self {
        let instrument = Instrument::Futures(
            FuturesContract::new(
                Asset::new("RB", AssetClass::Commodity).unwrap(),
                Asset::new("USD", AssetClass::Currency).unwrap(),
                Mic::xcme(),
                Currency::usd().into(),
                2008,
                Tenor::April,
                None,
            )
            .unwrap(),
        );
        let spec = Specification::new(
            Price::from_str_unchecked("0.0001"),
            (Price::from_str_unchecked("4.20"), Currency::usd().into()),
            Quantity::from_str_unchecked("1"),
            Quantity::from_str_unchecked("10"),
            QtyStep::new(Quantity::from_str_unchecked("1")).unwrap(),
        )
        .unwrap();
        let entry_time = time(10, 0, 0, 0);
        let entry_time_end = entry_time + SignedDuration::from_hours(2);
        // 1 min price flunctuation is 4.2$ => 500 flunctuations is 2_100$.
        // => flunctuations in price quotation should be 0.05
        let stop_loss_price_diff = Price::from_str_unchecked("0.05");

        Self {
            instrument,
            spec,
            listing: ListedTenors::monthly(),
            // RB terminates on the last business day of the month before delivery.
            // But liquidity ends much earlier.
            // (current_contract_volume, next_contract_volume) / sum(volumes) = 50/50
            // ~ 10 days before the end of trading
            eot: LastNthBDayOfPrevMonth::from_u8(1, DateOffset::BusinessDays(-10)),
            day_of_week: Weekday::Friday,
            exchange_tz: TimeZone::get("America/Chicago")
                .expect("the tz database has America/Chicago"),
            entry_time: (entry_time, entry_time_end),
            out_time: time(20, 0, 0, 0),
            stop_loss_price_diff,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let config = Config::default();

        let _ = dbg!(&config);
    }
}
