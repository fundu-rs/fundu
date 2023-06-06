// spell-checker: ignore econd inute onths nute nths econds inutes

use fundu::TimeUnit::*;
use fundu::{Config, Delimiter, Duration, Multiplier, ParseError, Parser, TimeUnit, TimeUnitsLike};

const DELIMITER: Delimiter = |byte| byte == b' ' || (byte >= 0x9 && byte <= 0xd);

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
            1 => match bytes[0] {
                b's' => Some(SECOND),
                b'm' => Some(MINUTE),
                b'h' => Some(HOUR),
                b'd' => Some(DAY),
                b'w' => Some(WEEK),
                b'M' => Some(MONTH),
                b'y' => Some(YEAR),
                _ => None,
            },
            2 => match bytes[0] {
                b'n' => bytes[1].eq(&b's').then_some(NANO_SECOND), // ns
                b'u' => bytes[1].eq(&b's').then_some(MICRO_SECOND), // us
                b'm' => bytes[1].eq(&b's').then_some(MILLI_SECOND), // ms
                b'h' => bytes[1].eq(&b'r').then_some(HOUR),        // hr
                _ => None,
            },
            3 => match bytes[0] {
                b'\xc2' => bytes[1..].eq(b"\xb5s").then_some(MICRO_SECOND), // µs
                b's' => bytes[1..].eq(b"ec").then_some(SECOND),             // sec
                b'm' => bytes[1..].eq(b"in").then_some(MINUTE),             // min
                b'd' => bytes[1..].eq(b"ay").then_some(DAY),                // day
                _ => None,
            },
            4 => match bytes[0] {
                b'n' => bytes[1..].eq(b"sec").then_some(NANO_SECOND), // nsec
                b'u' => bytes[1..].eq(b"sec").then_some(MICRO_SECOND), // usec
                b'm' => bytes[1..].eq(b"sec").then_some(MILLI_SECOND), // msec
                b'h' => bytes[1..].eq(b"our").then_some(HOUR),        // hour
                b'd' => bytes[1..].eq(b"ays").then_some(DAY),         // days
                b'w' => bytes[1..].eq(b"eek").then_some(WEEK),        // week
                b'y' => bytes[1..].eq(b"ear").then_some(YEAR),        // year
                _ => None,
            },
            5 => match bytes[0] {
                b'h' => bytes[1..].eq(b"ours").then_some(HOUR), // hours
                b'w' => bytes[1..].eq(b"eeks").then_some(WEEK), // weeks
                b'm' => bytes[1..].eq(b"onth").then_some(MONTH), // month
                b'y' => bytes[1..].eq(b"ears").then_some(YEAR), // years
                _ => None,
            },
            6 => match &bytes[0..1] {
                b"se" => bytes[2..].eq(b"cond").then_some(SECOND), // second
                b"mi" => bytes[2..].eq(b"nute").then_some(MINUTE), // minute
                b"mo" => bytes[2..].eq(b"nths").then_some(MONTH),  // months
                _ => None,
            },
            7 => match bytes[0] {
                b's' => bytes[1..].eq(b"econds").then_some(SECOND), // seconds
                b'm' => bytes[1..].eq(b"inutes").then_some(MINUTE), // minutes
                _ => None,
            },
            _ => None,
        }
    }
}
