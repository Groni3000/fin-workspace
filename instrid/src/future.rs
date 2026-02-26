use crate::{
    asset::Asset,
    exchange::Exchange,
    instrument::{Instrument, InstrumentParseError, TradeInstrument},
    tenor::{Tenor, TenorParseError},
};
use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

/// A futures contract, identified by an underlying instrument plus contract
/// year, month, optional day, and optional contract multiplier.
///
/// # Parsing format
/// `BASE/QUOTE@EXCHANGE#YYYY-MMM[-DD][*MULT]`
///
/// # Examples
/// ```
/// use instrid::future::Future;
/// use instrid::instrument::Instrument;
/// use instrid::asset::Asset;
/// use instrid::exchange::Exchange;
/// use instrid::tenor::Tenor;
///
/// let fut: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
/// assert_eq!(fut.year, 2025);
/// assert_eq!(fut.month, Tenor::June);
/// assert_eq!(fut.day, None);
/// assert_eq!(fut.multiplier, None);
///
/// let fut: Future = "ES/USD@CME#2025-SEP-15*50".parse().unwrap();
/// assert_eq!(fut.day, Some(15));
/// assert_eq!(fut.multiplier, Some(50.0));
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Future {
    pub instrument: Instrument,
    pub year: u16,
    pub month: Tenor,
    pub day: Option<u8>,
    pub multiplier: Option<f64>,
}

impl Future {
    pub const fn new(
        instrument: Instrument,
        year: u16,
        month: Tenor,
        day: Option<u8>,
        multiplier: Option<f64>,
    ) -> Self {
        Self {
            instrument,
            year,
            month,
            day,
            multiplier,
        }
    }
}

#[derive(Debug)]
pub enum FutureParseError {
    InvalidFormat,
    InvalidInstrument(InstrumentParseError),
    InvalidYear,
    InvalidMonth(TenorParseError),
    InvalidDay,
    InvalidMultiplier,
}

impl fmt::Display for FutureParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FutureParseError::InvalidFormat => write!(
                f,
                "invalid future format (expected BASE/QUOTE@EXCHANGE#YYYY-MMM[-DD][*MULT])"
            ),
            FutureParseError::InvalidInstrument(e) => {
                write!(f, "invalid future instrument: {}", e)
            }
            FutureParseError::InvalidYear => write!(f, "invalid contract year"),
            FutureParseError::InvalidMonth(e) => write!(f, "invalid contract month: {}", e),
            FutureParseError::InvalidDay => write!(f, "invalid contract day"),
            FutureParseError::InvalidMultiplier => write!(f, "invalid contract multiplier"),
        }
    }
}

impl std::error::Error for FutureParseError {}

impl FromStr for Future {
    type Err = FutureParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (instrument_str, contract_str) = s
            .split_once('#')
            .ok_or(FutureParseError::InvalidFormat)?;

        let instrument = instrument_str
            .parse::<Instrument>()
            .map_err(FutureParseError::InvalidInstrument)?;

        // Split off multiplier if present: "2025-JUN-15*50" -> ("2025-JUN-15", Some("50"))
        let (date_str, multiplier_str) = match contract_str.split_once('*') {
            Some((d, m)) => (d, Some(m)),
            None => (contract_str, None),
        };

        // Parse date parts: "2025-JUN" or "2025-JUN-15"
        let mut parts = date_str.splitn(3, '-');

        let year_str = parts.next().ok_or(FutureParseError::InvalidFormat)?;
        let year: u16 = year_str.parse().map_err(|_| FutureParseError::InvalidYear)?;

        let month_str = parts.next().ok_or(FutureParseError::InvalidFormat)?;
        let month: Tenor = month_str
            .parse()
            .map_err(FutureParseError::InvalidMonth)?;

        let day: Option<u8> = match parts.next() {
            Some(d) => {
                let day_val: u8 = d.parse().map_err(|_| FutureParseError::InvalidDay)?;
                if day_val == 0 || day_val > month.max_days() {
                    return Err(FutureParseError::InvalidDay);
                }
                Some(day_val)
            }
            None => None,
        };

        let multiplier: Option<f64> = match multiplier_str {
            Some(m) => {
                let val: f64 = m.parse().map_err(|_| FutureParseError::InvalidMultiplier)?;
                if val <= 0.0 || val.is_nan() || val.is_infinite() {
                    return Err(FutureParseError::InvalidMultiplier);
                }
                Some(val)
            }
            None => None,
        };

        Ok(Future::new(instrument, year, month, day, multiplier))
    }
}

impl fmt::Display for Future {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}#{}-{}", self.instrument, self.year, self.month)?;
        if let Some(day) = self.day {
            write!(f, "-{}", day)?;
        }
        if let Some(mult) = self.multiplier {
            if mult.fract() == 0.0 {
                write!(f, "*{}", mult as u64)?;
            } else {
                write!(f, "*{}", mult)?;
            }
        }
        Ok(())
    }
}

/// Compares futures by expiration date (year, month, day).
///
/// Contracts without a day (`None`) sort before contracts with a day in the
/// same year/month, treating `None` as "month-level expiry" (i.e. earlier
/// or equal to any specific day).
impl PartialOrd for Future {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(
            self.year
                .cmp(&other.year)
                .then(self.month.cmp(&other.month))
                .then(self.day.cmp(&other.day)),
        )
    }
}

impl TradeInstrument for Future {
    fn base(&self) -> &Asset {
        &self.instrument.base
    }
    fn quote(&self) -> &Asset {
        &self.instrument.quote
    }
    fn exchange(&self) -> &Exchange {
        &self.instrument.exchange
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // region: FromStr

    #[test]
    fn parse_basic() {
        let fut: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        assert_eq!(fut.instrument.base.code(), "CL");
        assert_eq!(fut.instrument.quote, Asset::USD);
        assert_eq!(fut.instrument.exchange, Exchange::NYMEX);
        assert_eq!(fut.year, 2025);
        assert_eq!(fut.month, Tenor::June);
        assert_eq!(fut.day, None);
        assert_eq!(fut.multiplier, None);
    }

    #[test]
    fn parse_with_day() {
        let fut: Future = "ES/USD@CME#2025-SEP-15".parse().unwrap();
        assert_eq!(fut.day, Some(15));
        assert_eq!(fut.multiplier, None);
    }

    #[test]
    fn parse_with_multiplier() {
        let fut: Future = "CL/USD@NYMEX#2025-JUN*1000".parse().unwrap();
        assert_eq!(fut.day, None);
        assert_eq!(fut.multiplier, Some(1000.0));
    }

    #[test]
    fn parse_with_day_and_multiplier() {
        let fut: Future = "ES/USD@CME#2025-SEP-15*50".parse().unwrap();
        assert_eq!(fut.day, Some(15));
        assert_eq!(fut.multiplier, Some(50.0));
    }

    #[test]
    fn parse_fractional_multiplier() {
        let fut: Future = "ZB/USD@CBOT#2025-DEC*31.25".parse().unwrap();
        assert_eq!(fut.multiplier, Some(31.25));
    }

    #[test]
    fn parse_missing_hash() {
        let result = "CL/USD@NYMEX2025-JUN".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidFormat)));
    }

    #[test]
    fn parse_invalid_instrument() {
        let result = "invalid#2025-JUN".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidInstrument(_))));
    }

    #[test]
    fn parse_invalid_year() {
        let result = "CL/USD@NYMEX#XXXX-JUN".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidYear)));
    }

    #[test]
    fn parse_invalid_month() {
        let result = "CL/USD@NYMEX#2025-XXX".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidMonth(_))));
    }

    #[test]
    fn parse_invalid_day() {
        let result = "CL/USD@NYMEX#2025-JUN-0".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidDay)));
    }

    #[test]
    fn parse_day_out_of_range() {
        let result = "CL/USD@NYMEX#2025-JUN-31".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidDay)));
    }

    #[test]
    fn parse_day_feb_30() {
        let result = "CL/USD@NYMEX#2025-FEB-30".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidDay)));
    }

    #[test]
    fn parse_invalid_multiplier() {
        let result = "CL/USD@NYMEX#2025-JUN*abc".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidMultiplier)));
    }

    #[test]
    fn parse_negative_multiplier() {
        let result = "CL/USD@NYMEX#2025-JUN*-1".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidMultiplier)));
    }

    #[test]
    fn parse_zero_multiplier() {
        let result = "CL/USD@NYMEX#2025-JUN*0".parse::<Future>();
        assert!(matches!(result, Err(FutureParseError::InvalidMultiplier)));
    }

    // endregion

    // region: Display / round-trip

    #[test]
    fn display_basic() {
        let fut: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        assert_eq!(fut.to_string(), "CL/USD@NYMEX#2025-JUN");
    }

    #[test]
    fn display_with_day() {
        let fut: Future = "ES/USD@CME#2025-SEP-15".parse().unwrap();
        assert_eq!(fut.to_string(), "ES/USD@CME#2025-SEP-15");
    }

    #[test]
    fn display_with_multiplier() {
        let fut: Future = "CL/USD@NYMEX#2025-JUN*1000".parse().unwrap();
        assert_eq!(fut.to_string(), "CL/USD@NYMEX#2025-JUN*1000");
    }

    #[test]
    fn display_with_day_and_multiplier() {
        let fut: Future = "ES/USD@CME#2025-SEP-15*50".parse().unwrap();
        assert_eq!(fut.to_string(), "ES/USD@CME#2025-SEP-15*50");
    }

    #[test]
    fn roundtrip() {
        let original: Future = "CL/USD@NYMEX#2025-JUN-15*1000".parse().unwrap();
        let displayed = original.to_string();
        let parsed: Future = displayed.parse().unwrap();
        assert_eq!(original, parsed);
    }

    // endregion

    // region: const construction

    #[test]
    fn const_construction() {
        const FUT: Future = Future::new(
            Instrument::new(Asset::BTC, Asset::USD, Exchange::CME),
            2025,
            Tenor::June,
            None,
            None,
        );
        assert_eq!(FUT.year, 2025);
        assert_eq!(FUT.month, Tenor::June);
    }

    // endregion

    // region: equality

    #[test]
    fn equality() {
        let a: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        let b: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn inequality_different_month() {
        let a: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        let b: Future = "CL/USD@NYMEX#2025-JUL".parse().unwrap();
        assert_ne!(a, b);
    }

    // endregion

    // region: TradeInstrument

    #[test]
    fn trade_instrument_trait() {
        let fut: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        assert_eq!(fut.base().code(), "CL");
        assert_eq!(fut.quote().code(), "USD");
        assert_eq!(fut.exchange().code(), "NYMEX");
    }

    // endregion

    // region: ordering (by expiration date)

    #[test]
    fn earlier_year_is_less() {
        let a: Future = "CL/USD@NYMEX#2024-JUN".parse().unwrap();
        let b: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        assert!(a < b);
    }

    #[test]
    fn earlier_month_is_less() {
        let a: Future = "CL/USD@NYMEX#2025-MAR".parse().unwrap();
        let b: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        assert!(a < b);
    }

    #[test]
    fn earlier_day_is_less() {
        let a: Future = "CL/USD@NYMEX#2025-JUN-1".parse().unwrap();
        let b: Future = "CL/USD@NYMEX#2025-JUN-15".parse().unwrap();
        assert!(a < b);
    }

    #[test]
    fn no_day_sorts_before_day() {
        let a: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        let b: Future = "CL/USD@NYMEX#2025-JUN-1".parse().unwrap();
        assert!(a < b);
    }

    #[test]
    fn same_expiration_is_equal_order() {
        let a: Future = "CL/USD@NYMEX#2025-JUN".parse().unwrap();
        let b: Future = "ES/USD@CME#2025-JUN".parse().unwrap();
        assert!(a.partial_cmp(&b) == Some(Ordering::Equal));
    }

    #[test]
    fn ordering_ignores_multiplier() {
        let a: Future = "CL/USD@NYMEX#2025-JUN*1000".parse().unwrap();
        let b: Future = "CL/USD@NYMEX#2025-JUN*50".parse().unwrap();
        assert!(a.partial_cmp(&b) == Some(Ordering::Equal));
    }

    #[test]
    fn sort_futures_by_expiration() {
        let mut futs: Vec<Future> = vec![
            "CL/USD@NYMEX#2025-DEC".parse().unwrap(),
            "CL/USD@NYMEX#2024-MAR".parse().unwrap(),
            "CL/USD@NYMEX#2025-JUN-15".parse().unwrap(),
            "CL/USD@NYMEX#2025-JUN".parse().unwrap(),
        ];
        futs.sort_by(|a, b| a.partial_cmp(b).unwrap());
        assert_eq!(futs[0].year, 2024);
        assert_eq!(futs[1].month, Tenor::June);
        assert_eq!(futs[1].day, None);
        assert_eq!(futs[2].month, Tenor::June);
        assert_eq!(futs[2].day, Some(15));
        assert_eq!(futs[3].month, Tenor::December);
    }

    // endregion
}
