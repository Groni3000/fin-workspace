use crate::{
    asset::Asset,
    exchange::Exchange,
    instrument::{Instrument, InstrumentParseError, TradeInstrument},
    tenor::{Tenor, TenorParseError},
};
use std::cmp::Ordering;
use std::fmt;
use std::str::FromStr;

/// Whether a financial option is a call or a put.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OptionType {
    Call,
    Put,
}

#[derive(Debug)]
pub struct OptionTypeParseError(String);

impl fmt::Display for OptionTypeParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid option type: '{}' (expected Call, Put, C, or P)",
            self.0
        )
    }
}

impl std::error::Error for OptionTypeParseError {}

impl FromStr for OptionType {
    type Err = OptionTypeParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "call" | "c" => Ok(OptionType::Call),
            "put" | "p" => Ok(OptionType::Put),
            _ => Err(OptionTypeParseError(s.to_string())),
        }
    }
}

impl fmt::Display for OptionType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OptionType::Call => f.write_str("CALL"),
            OptionType::Put => f.write_str("PUT"),
        }
    }
}

/// A financial option contract, identified by an underlying instrument,
/// contract date, optional multiplier, option type (call/put), and strike price.
///
/// # Parsing format
/// `BASE/QUOTE@EXCHANGE#YYYY-MMM[-DD][*MULT]:CALL|PUT$STRIKE`
///
/// # Examples
/// ```
/// use instrid::option_contract::{OptionContract, OptionType};
/// use instrid::tenor::Tenor;
///
/// let opt: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
/// assert_eq!(opt.option_type, OptionType::Call);
/// assert_eq!(opt.strike, 4500.0);
///
/// let opt: OptionContract = "CL/USD@NYMEX#2025-JUN-15*1000:PUT$75.50".parse().unwrap();
/// assert_eq!(opt.day, Some(15));
/// assert_eq!(opt.multiplier, Some(1000.0));
/// assert_eq!(opt.option_type, OptionType::Put);
/// assert_eq!(opt.strike, 75.50);
/// ```
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct OptionContract {
    pub instrument: Instrument,
    pub year: u16,
    pub month: Tenor,
    pub day: Option<u8>,
    pub multiplier: Option<f64>,
    pub option_type: OptionType,
    pub strike: f64,
}

impl OptionContract {
    pub const fn new(
        instrument: Instrument,
        year: u16,
        month: Tenor,
        day: Option<u8>,
        multiplier: Option<f64>,
        option_type: OptionType,
        strike: f64,
    ) -> Self {
        Self {
            instrument,
            year,
            month,
            day,
            multiplier,
            option_type,
            strike,
        }
    }
}

#[derive(Debug)]
pub enum OptionContractParseError {
    InvalidFormat,
    InvalidInstrument(InstrumentParseError),
    InvalidYear,
    InvalidMonth(TenorParseError),
    InvalidDay,
    InvalidMultiplier,
    InvalidOptionType(OptionTypeParseError),
    InvalidStrike,
}

impl fmt::Display for OptionContractParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OptionContractParseError::InvalidFormat => write!(
                f,
                "invalid option format (expected BASE/QUOTE@EXCHANGE#YYYY-MMM[-DD][*MULT]:CALL|PUT$STRIKE)"
            ),
            OptionContractParseError::InvalidInstrument(e) => {
                write!(f, "invalid option instrument: {}", e)
            }
            OptionContractParseError::InvalidYear => write!(f, "invalid contract year"),
            OptionContractParseError::InvalidMonth(e) => {
                write!(f, "invalid contract month: {}", e)
            }
            OptionContractParseError::InvalidDay => write!(f, "invalid contract day"),
            OptionContractParseError::InvalidMultiplier => {
                write!(f, "invalid contract multiplier")
            }
            OptionContractParseError::InvalidOptionType(e) => {
                write!(f, "invalid option type: {}", e)
            }
            OptionContractParseError::InvalidStrike => write!(f, "invalid strike price"),
        }
    }
}

impl std::error::Error for OptionContractParseError {}

impl FromStr for OptionContract {
    type Err = OptionContractParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Split: instrument#contract:option_type$strike
        let (instrument_str, rest) = s
            .split_once('#')
            .ok_or(OptionContractParseError::InvalidFormat)?;

        let instrument = instrument_str
            .parse::<Instrument>()
            .map_err(OptionContractParseError::InvalidInstrument)?;

        // Split contract part from option part at ':'
        let (contract_str, option_str) = rest
            .split_once(':')
            .ok_or(OptionContractParseError::InvalidFormat)?;

        // Split option type from strike at '$'
        let (type_str, strike_str) = option_str
            .split_once('$')
            .ok_or(OptionContractParseError::InvalidFormat)?;

        let option_type: OptionType = type_str
            .parse()
            .map_err(OptionContractParseError::InvalidOptionType)?;

        let strike: f64 = strike_str
            .parse()
            .map_err(|_| OptionContractParseError::InvalidStrike)?;
        if strike < 0.0 || strike.is_nan() || strike.is_infinite() {
            return Err(OptionContractParseError::InvalidStrike);
        }

        // Split off multiplier if present
        let (date_str, multiplier_str) = match contract_str.split_once('*') {
            Some((d, m)) => (d, Some(m)),
            None => (contract_str, None),
        };

        // Parse date parts
        let mut parts = date_str.splitn(3, '-');

        let year_str = parts.next().ok_or(OptionContractParseError::InvalidFormat)?;
        let year: u16 = year_str
            .parse()
            .map_err(|_| OptionContractParseError::InvalidYear)?;

        let month_str = parts
            .next()
            .ok_or(OptionContractParseError::InvalidFormat)?;
        let month: Tenor = month_str
            .parse()
            .map_err(OptionContractParseError::InvalidMonth)?;

        let day: Option<u8> = match parts.next() {
            Some(d) => {
                let day_val: u8 = d
                    .parse()
                    .map_err(|_| OptionContractParseError::InvalidDay)?;
                if day_val == 0 || day_val > month.max_days() {
                    return Err(OptionContractParseError::InvalidDay);
                }
                Some(day_val)
            }
            None => None,
        };

        let multiplier: Option<f64> = match multiplier_str {
            Some(m) => {
                let val: f64 = m
                    .parse()
                    .map_err(|_| OptionContractParseError::InvalidMultiplier)?;
                if val <= 0.0 || val.is_nan() || val.is_infinite() {
                    return Err(OptionContractParseError::InvalidMultiplier);
                }
                Some(val)
            }
            None => None,
        };

        Ok(OptionContract::new(
            instrument,
            year,
            month,
            day,
            multiplier,
            option_type,
            strike,
        ))
    }
}

impl fmt::Display for OptionContract {
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
        write!(f, ":{}$", self.option_type)?;
        if self.strike.fract() == 0.0 {
            write!(f, "{}", self.strike as u64)
        } else {
            write!(f, "{}", self.strike)
        }
    }
}

/// Compares option contracts by expiration date (year, month, day).
///
/// Contracts without a day (`None`) sort before contracts with a day in the
/// same year/month, treating `None` as "month-level expiry" (i.e. earlier
/// or equal to any specific day).
impl PartialOrd for OptionContract {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(
            self.year
                .cmp(&other.year)
                .then(self.month.cmp(&other.month))
                .then(self.day.cmp(&other.day)),
        )
    }
}

impl TradeInstrument for OptionContract {
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

    // region: OptionType

    #[test]
    fn parse_option_type_call() {
        assert_eq!("Call".parse::<OptionType>().unwrap(), OptionType::Call);
        assert_eq!("CALL".parse::<OptionType>().unwrap(), OptionType::Call);
        assert_eq!("call".parse::<OptionType>().unwrap(), OptionType::Call);
        assert_eq!("C".parse::<OptionType>().unwrap(), OptionType::Call);
        assert_eq!("c".parse::<OptionType>().unwrap(), OptionType::Call);
    }

    #[test]
    fn parse_option_type_put() {
        assert_eq!("Put".parse::<OptionType>().unwrap(), OptionType::Put);
        assert_eq!("PUT".parse::<OptionType>().unwrap(), OptionType::Put);
        assert_eq!("put".parse::<OptionType>().unwrap(), OptionType::Put);
        assert_eq!("P".parse::<OptionType>().unwrap(), OptionType::Put);
        assert_eq!("p".parse::<OptionType>().unwrap(), OptionType::Put);
    }

    #[test]
    fn parse_option_type_invalid() {
        assert!("X".parse::<OptionType>().is_err());
        assert!("".parse::<OptionType>().is_err());
    }

    #[test]
    fn display_option_type() {
        assert_eq!(OptionType::Call.to_string(), "CALL");
        assert_eq!(OptionType::Put.to_string(), "PUT");
    }

    // endregion

    // region: FromStr

    #[test]
    fn parse_basic_call() {
        let opt: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        assert_eq!(opt.instrument.base.code(), "ES");
        assert_eq!(opt.instrument.quote, Asset::USD);
        assert_eq!(opt.instrument.exchange, Exchange::CME);
        assert_eq!(opt.year, 2025);
        assert_eq!(opt.month, Tenor::September);
        assert_eq!(opt.day, None);
        assert_eq!(opt.multiplier, None);
        assert_eq!(opt.option_type, OptionType::Call);
        assert_eq!(opt.strike, 4500.0);
    }

    #[test]
    fn parse_basic_put() {
        let opt: OptionContract = "CL/USD@NYMEX#2025-JUN:PUT$75.50".parse().unwrap();
        assert_eq!(opt.option_type, OptionType::Put);
        assert_eq!(opt.strike, 75.50);
    }

    #[test]
    fn parse_with_day_and_multiplier() {
        let opt: OptionContract =
            "CL/USD@NYMEX#2025-JUN-15*1000:PUT$75.50".parse().unwrap();
        assert_eq!(opt.day, Some(15));
        assert_eq!(opt.multiplier, Some(1000.0));
        assert_eq!(opt.option_type, OptionType::Put);
        assert_eq!(opt.strike, 75.50);
    }

    #[test]
    fn parse_missing_hash() {
        let result = "ES/USD@CME2025-SEP:CALL$4500".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidFormat)
        ));
    }

    #[test]
    fn parse_missing_colon() {
        let result = "ES/USD@CME#2025-SEPCALL$4500".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidFormat)
        ));
    }

    #[test]
    fn parse_missing_dollar() {
        let result = "ES/USD@CME#2025-SEP:CALL4500".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidFormat)
        ));
    }

    #[test]
    fn parse_invalid_strike() {
        let result = "ES/USD@CME#2025-SEP:CALL$abc".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidStrike)
        ));
    }

    #[test]
    fn parse_invalid_option_type() {
        let result = "ES/USD@CME#2025-SEP:BUY$4500".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidOptionType(_))
        ));
    }

    #[test]
    fn parse_invalid_day() {
        let result = "ES/USD@CME#2025-SEP-0:CALL$4500".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidDay)
        ));
    }

    #[test]
    fn parse_day_exceeds_month() {
        let result = "ES/USD@CME#2025-FEB-30:CALL$4500".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidDay)
        ));
    }

    #[test]
    fn parse_negative_multiplier() {
        let result = "ES/USD@CME#2025-SEP*-5:CALL$4500".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidMultiplier)
        ));
    }

    #[test]
    fn parse_zero_multiplier() {
        let result = "ES/USD@CME#2025-SEP*0:CALL$4500".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidMultiplier)
        ));
    }

    #[test]
    fn parse_negative_strike() {
        let result = "ES/USD@CME#2025-SEP:CALL$-100".parse::<OptionContract>();
        assert!(matches!(
            result,
            Err(OptionContractParseError::InvalidStrike)
        ));
    }

    // endregion

    // region: Display / round-trip

    #[test]
    fn display_basic_call() {
        let opt: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        assert_eq!(opt.to_string(), "ES/USD@CME#2025-SEP:CALL$4500");
    }

    #[test]
    fn display_put_with_decimal_strike() {
        let opt: OptionContract = "CL/USD@NYMEX#2025-JUN:PUT$75.50".parse().unwrap();
        assert_eq!(opt.to_string(), "CL/USD@NYMEX#2025-JUN:PUT$75.5");
    }

    #[test]
    fn display_with_day_and_multiplier() {
        let opt: OptionContract =
            "CL/USD@NYMEX#2025-JUN-15*1000:PUT$75".parse().unwrap();
        assert_eq!(opt.to_string(), "CL/USD@NYMEX#2025-JUN-15*1000:PUT$75");
    }

    #[test]
    fn roundtrip() {
        let original: OptionContract =
            "ES/USD@CME#2025-SEP-15*50:CALL$4500".parse().unwrap();
        let displayed = original.to_string();
        let parsed: OptionContract = displayed.parse().unwrap();
        assert_eq!(original, parsed);
    }

    // endregion

    // region: const construction

    #[test]
    fn const_construction() {
        const OPT: OptionContract = OptionContract::new(
            Instrument::new(Asset::BTC, Asset::USD, Exchange::CME),
            2025,
            Tenor::September,
            None,
            None,
            OptionType::Call,
            50000.0,
        );
        assert_eq!(OPT.option_type, OptionType::Call);
        assert_eq!(OPT.strike, 50000.0);
    }

    // endregion

    // region: equality

    #[test]
    fn equality() {
        let a: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        let b: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        assert_eq!(a, b);
    }

    #[test]
    fn inequality_different_type() {
        let a: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        let b: OptionContract = "ES/USD@CME#2025-SEP:PUT$4500".parse().unwrap();
        assert_ne!(a, b);
    }

    #[test]
    fn inequality_different_strike() {
        let a: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        let b: OptionContract = "ES/USD@CME#2025-SEP:CALL$4600".parse().unwrap();
        assert_ne!(a, b);
    }

    // endregion

    // region: TradeInstrument

    #[test]
    fn trade_instrument_trait() {
        let opt: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        assert_eq!(opt.base().code(), "ES");
        assert_eq!(opt.quote().code(), "USD");
        assert_eq!(opt.exchange().code(), "CME");
    }

    // endregion

    // region: ordering (by expiration date)

    #[test]
    fn earlier_year_is_less() {
        let a: OptionContract = "ES/USD@CME#2024-SEP:CALL$4500".parse().unwrap();
        let b: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        assert!(a < b);
    }

    #[test]
    fn earlier_month_is_less() {
        let a: OptionContract = "ES/USD@CME#2025-MAR:CALL$4500".parse().unwrap();
        let b: OptionContract = "ES/USD@CME#2025-SEP:CALL$4500".parse().unwrap();
        assert!(a < b);
    }

    #[test]
    fn earlier_day_is_less() {
        let a: OptionContract = "ES/USD@CME#2025-SEP-1:CALL$4500".parse().unwrap();
        let b: OptionContract = "ES/USD@CME#2025-SEP-15:CALL$4500".parse().unwrap();
        assert!(a < b);
    }

    #[test]
    fn ordering_ignores_strike_and_type() {
        let a: OptionContract = "ES/USD@CME#2025-SEP:CALL$5000".parse().unwrap();
        let b: OptionContract = "ES/USD@CME#2025-SEP:PUT$4000".parse().unwrap();
        assert!(a.partial_cmp(&b) == Some(Ordering::Equal));
    }

    #[test]
    fn sort_options_by_expiration() {
        let mut opts: Vec<OptionContract> = vec![
            "ES/USD@CME#2025-DEC:PUT$4500".parse().unwrap(),
            "ES/USD@CME#2024-MAR:CALL$4000".parse().unwrap(),
            "ES/USD@CME#2025-JUN:CALL$4200".parse().unwrap(),
        ];
        opts.sort_by(|a, b| a.partial_cmp(b).unwrap());
        assert_eq!(opts[0].year, 2024);
        assert_eq!(opts[1].month, Tenor::June);
        assert_eq!(opts[2].month, Tenor::December);
    }

    // endregion
}
