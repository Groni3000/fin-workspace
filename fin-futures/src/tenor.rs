use std::fmt;
use std::str::FromStr;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Tenor {
    January = 1,
    February = 2,
    March = 3,
    April = 4,
    May = 5,
    June = 6,
    July = 7,
    August = 8,
    September = 9,
    October = 10,
    November = 11,
    December = 12,
}

impl Tenor {
    pub fn ordinal(&self) -> u8 {
        *self as u8
    }

    pub fn from_ordinal(n: u8) -> Option<Self> {
        match n {
            1 => Some(Tenor::January),
            2 => Some(Tenor::February),
            3 => Some(Tenor::March),
            4 => Some(Tenor::April),
            5 => Some(Tenor::May),
            6 => Some(Tenor::June),
            7 => Some(Tenor::July),
            8 => Some(Tenor::August),
            9 => Some(Tenor::September),
            10 => Some(Tenor::October),
            11 => Some(Tenor::November),
            12 => Some(Tenor::December),
            _ => None,
        }
    }
}

#[derive(Debug)]
pub struct TenorParseError(String);

impl fmt::Display for TenorParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid tenor: '{}' (expected month name or number 1-12)",
            self.0
        )
    }
}

impl std::error::Error for TenorParseError {}

impl FromStr for Tenor {
    type Err = TenorParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "january" | "jan" | "1" => Ok(Tenor::January),
            "february" | "feb" | "2" => Ok(Tenor::February),
            "march" | "mar" | "3" => Ok(Tenor::March),
            "april" | "apr" | "4" => Ok(Tenor::April),
            "may" | "5" => Ok(Tenor::May),
            "june" | "jun" | "6" => Ok(Tenor::June),
            "july" | "jul" | "7" => Ok(Tenor::July),
            "august" | "aug" | "8" => Ok(Tenor::August),
            "september" | "sep" | "9" => Ok(Tenor::September),
            "october" | "oct" | "10" => Ok(Tenor::October),
            "november" | "nov" | "11" => Ok(Tenor::November),
            "december" | "dec" | "12" => Ok(Tenor::December),
            _ => Err(TenorParseError(s.to_string())),
        }
    }
}

impl fmt::Display for Tenor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Tenor::January => "January",
            Tenor::February => "February",
            Tenor::March => "March",
            Tenor::April => "April",
            Tenor::May => "May",
            Tenor::June => "June",
            Tenor::July => "July",
            Tenor::August => "August",
            Tenor::September => "September",
            Tenor::October => "October",
            Tenor::November => "November",
            Tenor::December => "December",
        };
        f.write_str(s)
    }
}
