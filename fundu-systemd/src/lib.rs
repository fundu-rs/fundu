// spell-checker: ignore econd inute onths nute nths econds inutes

use fundu::TimeUnit::*;
use fundu::{Config, Delimiter, Duration, Multiplier, ParseError, Parser, TimeUnit, TimeUnitsLike};

const DELIMITER: Delimiter = |byte| matches!(byte, b' ' | 0x9..=0xd);

const CONFIG: Config = Config {
    allow_delimiter: Some(DELIMITER),
    default_unit: TimeUnit::Second,
    default_multiplier: Multiplier(1, 0),
    disable_exponent: true,
    disable_fraction: true,
    disable_infinity: true,
    number_is_optional: true,
    max_exponent: i16::MAX,
    min_exponent: i16::MIN,
    parse_multiple_delimiter: Some(DELIMITER),
    parse_multiple_conjunctions: None,
    allow_negative: false,
    allow_ago: None,
};

const TIME_UNITS: TimeUnits = TimeUnits {};

const NANO_SECOND: (TimeUnit, Multiplier) = (NanoSecond, NanoSecond.multiplier());
const MICRO_SECOND: (TimeUnit, Multiplier) = (MicroSecond, MicroSecond.multiplier());
const MILLI_SECOND: (TimeUnit, Multiplier) = (MilliSecond, MilliSecond.multiplier());
const SECOND: (TimeUnit, Multiplier) = (Second, Second.multiplier());
const MINUTE: (TimeUnit, Multiplier) = (Minute, Minute.multiplier());
const HOUR: (TimeUnit, Multiplier) = (Hour, Hour.multiplier());
const DAY: (TimeUnit, Multiplier) = (Day, Day.multiplier());
const WEEK: (TimeUnit, Multiplier) = (Week, Week.multiplier());
const MONTH: (TimeUnit, Multiplier) = (Month, Month.multiplier());
const YEAR: (TimeUnit, Multiplier) = (Year, Year.multiplier());
pub struct TimeSpanParser<'a> {
    parser: Parser<'a>,
}

impl<'a> TimeSpanParser<'a> {
    pub const fn new() -> Self {
        Self {
            parser: Parser::with_config(CONFIG),
        }
    }

    #[inline]
    pub fn parse(&self, source: &str) -> Result<Duration, ParseError> {
        self.parser.parse(source, &TIME_UNITS, None)
    }
}

impl<'a> Default for TimeSpanParser<'a> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct TimeUnits {}

impl TimeUnitsLike for TimeUnits {
    #[inline]
    fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        let bytes = identifier.as_bytes();
        match bytes.len() {
            1 => match bytes {
                b"s" => Some(SECOND),
                b"m" => Some(MINUTE),
                b"h" => Some(HOUR),
                b"d" => Some(DAY),
                b"w" => Some(WEEK),
                b"M" => Some(MONTH),
                b"y" => Some(YEAR),
                _ => None,
            },
            2 => match bytes {
                b"ns" => Some(NANO_SECOND),
                b"us" => Some(MICRO_SECOND),
                b"ms" => Some(MILLI_SECOND),
                b"hr" => Some(HOUR),
                _ => None,
            },
            3 => match bytes {
                b"\xc2\xb5s" => Some(MICRO_SECOND),
                b"sec" => Some(SECOND),
                b"min" => Some(MINUTE),
                b"day" => Some(DAY),
                _ => None,
            },
            4 => match bytes {
                b"nsec" => Some(NANO_SECOND),
                b"usec" => Some(MICRO_SECOND),
                b"msec" => Some(MILLI_SECOND),
                b"hour" => Some(HOUR),
                b"days" => Some(DAY),
                b"week" => Some(WEEK),
                b"year" => Some(YEAR),
                _ => None,
            },
            5 => match bytes {
                b"hours" => Some(HOUR),
                b"weeks" => Some(WEEK),
                b"month" => Some(MONTH),
                b"years" => Some(YEAR),
                _ => None,
            },
            6 => match bytes {
                b"second" => Some(SECOND),
                b"minute" => Some(MINUTE),
                b"months" => Some(MONTH),
                _ => None,
            },
            7 => match bytes {
                b"seconds" => Some(SECOND),
                b"minutes" => Some(MINUTE),
                _ => None,
            },
            _ => None,
        }
    }
}
