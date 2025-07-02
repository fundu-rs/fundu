// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! A simple to use, fast and precise gnu relative time parser fully compatible with the [gnu
//! relative time
//! format](https://www.gnu.org/software/coreutils/manual/html_node/Relative-items-in-date-strings.html)
//!
//! `fundu-gnu` can parse rust strings like
//!
//! `&str` | Duration |
//! -- | -- |
//! `"1hour"`| `Duration::positive(60 * 60, 0)` |
//! `"minute"`| `Duration::positive(60, 0)` |
//! `"2 hours"`| `Duration::positive(2 * 60 * 60, 0)` |
//! `"-3minutes"`| `Duration::negative(3 * 60, 0)` |
//! `"3 mins ago"`| `Duration::negative(3 * 60, 0)` |
//! `"999sec +1day"`| `Duration::positive(86_400 + 999, 0)` |
//! `"55secs500week"`| `Duration::positive(55 + 500 * 604_800, 0)` |
//! `"123456789"`| `Duration::positive(123_456_789, 0)` |
//! `"42fortnight"`| `Duration::positive(42 * 2 * 604_800, 0)` |
//! `"yesterday"`| `Duration::negative(24 * 60 * 60, 0)` |
//! `"now"`| `Duration::positive(0, 0)` |
//! `"today -10seconds"`| `Duration::negative(10, 0)` |
//!
//! `fundu` parses into its own [`Duration`] which is a superset of other `Durations` like
//! [`std::time::Duration`], [`chrono::Duration`] and [`time::Duration`]. See the
//! [documentation](https://docs.rs/fundu/latest/fundu/index.html#fundus-duration) how to easily
//! handle the conversion between these durations.
//!
//! # The Format
//! Supported time units:
//!
//! - `seconds`, `second`, `secs`, `sec`
//! - `minutes`, `minute`, `mins`, `min`
//! - `hours`, `hour`
//! - `days`, `day`
//! - `weeks`, `week`
//! - `fortnights`, `fortnight` (2 weeks)
//! - `months`, `month` (fuzzy)
//! - `years`, `year` (fuzzy)
//!
//! Fuzzy time units are not all of equal duration and depend on a given date. If no date is given
//! when parsing, the system time of `now` in UTC +0 is assumed.
//!
//! The special keywords `yesterday` worth `-1 day`, `tomorrow` worth `+1 day`, `today` and `now`
//! each worth a zero duration are allowed, too. These keywords count as a full duration and don't
//! accept a number, time unit or the `ago` time unit suffix.
//!
//! Summary of the rest of the format:
//!
//! - Only numbers like `"123 days"` and without exponent (like `"3e9 days"`) are allowed. Only
//!   seconds time units allow a fraction (like in `"1.123456 secs"`)
//! - Multiple durations like `"1sec 2min"` or `"1week2secs"` in the source string accumulate
//! - Time units without a number (like in `"second"`) are allowed and a value of `1` is assumed.
//! - The parsed duration represents the value exactly (without rounding errors as would occur in
//!   floating point calculations) as it is specified in the source string.
//! - The maximum supported duration (`Duration::MAX`) has `u64::MAX` seconds
//!   (`18_446_744_073_709_551_615`) and `999_999_999` nano seconds
//! - parsed durations larger than the maximum duration saturate at the maximum duration
//! - Negative durations like `"-1min"` or `"1 week ago"` are allowed
//! - Any leading, trailing whitespace or whitespace between the number and the time unit (like in
//!   `"1 \n sec"`) and multiple durations (like in `"1week \n 2minutes"`) is ignored and follows
//!   the posix definition of whitespace which is:
//!     - Space (`' '`)
//!     - Horizontal Tab (`'\x09'`)
//!     - Line Feed (`'\x0A'`)
//!     - Vertical Tab (`'\x0B'`)
//!     - Form Feed (`'\x0C'`)
//!     - Carriage Return (`'\x0D'`)
//!
//! Please see also the gnu
//! [documentation](https://www.gnu.org/software/coreutils/manual/html_node/Relative-items-in-date-strings.html)
//! for a description of their format.
//!
//! # Examples
//!
//! ```rust
//! use fundu_gnu::{Duration, RelativeTimeParser};
//!
//! let parser = RelativeTimeParser::new();
//! assert_eq!(parser.parse("1hour"), Ok(Duration::positive(60 * 60, 0)));
//! assert_eq!(parser.parse("minute"), Ok(Duration::positive(60, 0)));
//! assert_eq!(
//!     parser.parse("2 hours"),
//!     Ok(Duration::positive(2 * 60 * 60, 0))
//! );
//! assert_eq!(parser.parse("second"), Ok(Duration::positive(1, 0)));
//! assert_eq!(parser.parse("-3minutes"), Ok(Duration::negative(3 * 60, 0)));
//! assert_eq!(
//!     parser.parse("3 mins ago"),
//!     Ok(Duration::negative(3 * 60, 0))
//! );
//! assert_eq!(
//!     parser.parse("999sec +1day"),
//!     Ok(Duration::positive(86_400 + 999, 0))
//! );
//! assert_eq!(
//!     parser.parse("55secs500week"),
//!     Ok(Duration::positive(55 + 500 * 7 * 24 * 60 * 60, 0))
//! );
//! assert_eq!(
//!     parser.parse("300mins20secs 5hour"),
//!     Ok(Duration::positive(300 * 60 + 20 + 5 * 60 * 60, 0))
//! );
//! assert_eq!(
//!     parser.parse("123456789"),
//!     Ok(Duration::positive(123_456_789, 0))
//! );
//! assert_eq!(
//!     parser.parse("42fortnight"),
//!     Ok(Duration::positive(42 * 2 * 7 * 24 * 60 * 60, 0))
//! );
//! assert_eq!(
//!     parser.parse("yesterday"),
//!     Ok(Duration::negative(24 * 60 * 60, 0))
//! );
//! assert_eq!(parser.parse("now"), Ok(Duration::positive(0, 0)));
//! assert_eq!(
//!     parser.parse("today -10seconds"),
//!     Ok(Duration::negative(10, 0))
//! );
//! ```
//!
//! If parsing fuzzy units then the fuzz can cause different [`Duration`] based on the given
//! [`DateTime`]:
//!
//! ```rust
//! use fundu_gnu::{DateTime, Duration, RelativeTimeParser};
//!
//! let parser = RelativeTimeParser::new();
//! let date_time = DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0);
//! assert_eq!(
//!     parser.parse_with_date("+1year", Some(date_time)),
//!     Ok(Duration::positive(365 * 86400, 0))
//! );
//! assert_eq!(
//!     parser.parse_with_date("+2month", Some(date_time)),
//!     Ok(Duration::positive((31 + 28) * 86400, 0))
//! );
//!
//! // 1972 is a leap year
//! let date_time = DateTime::from_gregorian_date_time(1972, 1, 1, 0, 0, 0, 0);
//! assert_eq!(
//!     parser.parse_with_date("+1year", Some(date_time)),
//!     Ok(Duration::positive(366 * 86400, 0))
//! );
//! assert_eq!(
//!     parser.parse_with_date("+2month", Some(date_time)),
//!     Ok(Duration::positive((31 + 29) * 86400, 0))
//! );
//! ```
//!
//! If parsing fuzzy units with [`RelativeTimeParser::parse`], the [`DateTime`] of `now` in UTC +0
//! is assumed.
//!
//! The global [`parse`] method does the same without the need to create a [`RelativeTimeParser`].
//!
//! ```rust
//! use fundu_gnu::{parse, Duration};
//!
//! assert_eq!(parse("123 sec"), Ok(Duration::positive(123, 0)));
//! assert_eq!(parse("1sec3min"), Ok(Duration::positive(1 + 3 * 60, 0)));
//! ```
//!
//! Convert fundu's `Duration` into a [`std::time::Duration`]. Converting to [`chrono::Duration`] or
//! [`time::Duration`] works the same but needs the `chrono` or `time` feature activated.
//!
//! ```rust
//! use fundu_gnu::{parse, SaturatingInto};
//!
//! let duration = parse("123 sec").unwrap();
//! assert_eq!(
//!     TryInto::<std::time::Duration>::try_into(duration),
//!     Ok(std::time::Duration::new(123, 0))
//! );
//!
//! // With saturating_into the duration will saturate at the minimum and maximum of
//! // std::time::Duration, so for negative values at std::time::Duration::ZERO and for positive values
//! // at std::time::Duration::MAX
//! assert_eq!(
//!     SaturatingInto::<std::time::Duration>::saturating_into(duration),
//!     std::time::Duration::new(123, 0)
//! );
//! ```
//!
//! [`chrono::Duration`]: https://docs.rs/chrono/latest/chrono/struct.Duration.html
//! [`time::Duration`]: https://docs.rs/time/latest/time/struct.Duration.html

#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc(test(attr(warn(unused))))]
#![doc(test(attr(allow(unused_extern_crates))))]
#![warn(missing_docs)]
#![warn(clippy::pedantic)]
#![warn(clippy::default_numeric_fallback)]
#![warn(clippy::else_if_without_else)]
#![warn(clippy::fn_to_numeric_cast_any)]
#![warn(clippy::get_unwrap)]
#![warn(clippy::if_then_some_else_none)]
#![warn(clippy::mixed_read_write_in_expression)]
#![warn(clippy::partial_pub_fields)]
#![warn(clippy::rest_pat_in_fully_bound_structs)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_to_string)]
#![warn(clippy::todo)]
#![warn(clippy::try_err)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::unneeded_field_pattern)]
#![allow(clippy::must_use_candidate)]
#![allow(clippy::return_self_not_must_use)]
#![allow(clippy::enum_glob_use)]
#![allow(clippy::module_name_repetitions)]

macro_rules! validate {
    ($id:ident, $min:expr, $max:expr) => {{
        #[allow(unused_comparisons)]
        if $id < $min || $id > $max {
            panic!(concat!(
                "Invalid ",
                stringify!($id),
                ": Valid range is ",
                stringify!($min),
                " <= ",
                stringify!($id),
                " <= ",
                stringify!($max)
            ));
        }
    }};

    ($id:ident <= $max:expr) => {{
        #[allow(unused_comparisons)]
        if $id > $max {
            panic!(concat!(
                "Invalid ",
                stringify!($id),
                ": Valid maximum ",
                stringify!($id),
                " is ",
                stringify!($max)
            ));
        }
    }};
}

mod datetime;
mod util;

pub use datetime::{DateTime, JulianDay};
use fundu_core::config::{Config, ConfigBuilder, Delimiter, NumbersLike};
pub use fundu_core::error::{ParseError, TryFromDurationError};
use fundu_core::parse::{
    DurationRepr, Fract, Parser, ReprParserMultiple, ReprParserTemplate, Whole,
};
use fundu_core::time::TimeUnit::*;
pub use fundu_core::time::{Duration, SaturatingInto};
use fundu_core::time::{Multiplier, TimeUnit, TimeUnitsLike};
#[cfg(test)]
pub use rstest_reuse;
use util::{to_lowercase_u64, trim_whitespace};

// whitespace definition of: b' ', b'\x09', b'\x0A', b'\x0B', b'\x0C', b'\x0D'
const DELIMITER: Delimiter = |byte| byte == b' ' || byte.wrapping_sub(9) < 5;

const CONFIG: Config = ConfigBuilder::new()
    .allow_time_unit_delimiter()
    .allow_ago()
    .disable_exponent()
    .disable_infinity()
    .allow_negative()
    .number_is_optional()
    .parse_multiple(None)
    .allow_sign_delimiter()
    .inner_delimiter(DELIMITER)
    .outer_delimiter(DELIMITER)
    .build();

const TIME_UNITS: TimeUnits = TimeUnits {};
const TIME_KEYWORDS: TimeKeywords = TimeKeywords {};
const NUMERALS: Numerals = Numerals {};

const SECOND_UNIT: (TimeUnit, Multiplier) = (Second, Multiplier(1, 0));
const MINUTE_UNIT: (TimeUnit, Multiplier) = (Minute, Multiplier(1, 0));
const HOUR_UNIT: (TimeUnit, Multiplier) = (Hour, Multiplier(1, 0));
const DAY_UNIT: (TimeUnit, Multiplier) = (Day, Multiplier(1, 0));
const WEEK_UNIT: (TimeUnit, Multiplier) = (Week, Multiplier(1, 0));
const FORTNIGHT_UNIT: (TimeUnit, Multiplier) = (Week, Multiplier(2, 0));
const MONTH_UNIT: (TimeUnit, Multiplier) = (Month, Multiplier(1, 0));
const YEAR_UNIT: (TimeUnit, Multiplier) = (Year, Multiplier(1, 0));

const PARSER: RelativeTimeParser<'static> = RelativeTimeParser::new();

enum FuzzyUnit {
    Month,
    Year,
}

struct FuzzyTime {
    unit: FuzzyUnit,
    value: i64,
}

impl FuzzyTime {}

enum ParseFuzzyOutput {
    Duration(Duration),
    FuzzyTime(FuzzyTime),
}

struct DurationReprParser<'a>(DurationRepr<'a>);

impl DurationReprParser<'_> {
    fn parse(&mut self) -> Result<Duration, ParseError> {
        let is_negative = self.0.is_negative.unwrap_or_default();
        let time_unit = self.0.unit.unwrap_or(self.0.default_unit);

        let digits = self.0.input;
        match (&self.0.whole, &self.0.fract) {
            (None, None) if self.0.numeral.is_some() => {
                let Multiplier(coefficient, exponent) =
                    self.0.numeral.unwrap() * time_unit.multiplier() * self.0.multiplier;
                Ok(self
                    .0
                    .parse_duration_with_fixed_number(coefficient, exponent))
            }
            (None, None) if self.0.unit.is_some() => {
                let Multiplier(coefficient, _) = time_unit.multiplier() * self.0.multiplier;
                let duration_is_negative = is_negative ^ coefficient.is_negative();
                Ok(DurationRepr::calculate_duration(
                    duration_is_negative,
                    1,
                    0,
                    coefficient,
                ))
            }
            (None, None) => {
                unreachable!() // cov:excl-line
            }
            (None, Some(_)) if time_unit == TimeUnit::Second => Err(ParseError::InvalidInput(
                "Fraction without a whole number".to_owned(),
            )),
            (Some(whole), None) => {
                let Multiplier(coefficient, _) = time_unit.multiplier() * self.0.multiplier;
                let duration_is_negative = is_negative ^ coefficient.is_negative();
                let (seconds, attos) = match Whole::parse(&digits[whole.0..whole.1], None, None) {
                    Some(seconds) => (seconds, 0),
                    None if duration_is_negative => return Ok(Duration::MIN),
                    None => return Ok(Duration::MAX),
                };
                Ok(DurationRepr::calculate_duration(
                    duration_is_negative,
                    seconds,
                    attos,
                    coefficient,
                ))
            }
            (Some(_), Some(fract)) if time_unit == TimeUnit::Second && fract.is_empty() => Err(
                ParseError::InvalidInput("Fraction without a fractional number".to_owned()),
            ),
            (Some(whole), Some(fract)) if time_unit == TimeUnit::Second => {
                let Multiplier(coefficient, _) = time_unit.multiplier() * self.0.multiplier;
                let duration_is_negative = is_negative ^ coefficient.is_negative();
                let (seconds, attos) = match Whole::parse(&digits[whole.0..whole.1], None, None) {
                    Some(seconds) => (seconds, Fract::parse(&digits[fract.0..fract.1], None, None)),
                    None if duration_is_negative => return Ok(Duration::MIN),
                    None => return Ok(Duration::MAX),
                };
                Ok(DurationRepr::calculate_duration(
                    duration_is_negative,
                    seconds,
                    attos,
                    coefficient,
                ))
            }
            (Some(_) | None, Some(_)) => Err(ParseError::InvalidInput(
                "Fraction only allowed together with seconds as time unit".to_owned(),
            )),
        }
    }

    fn parse_fuzzy(&mut self) -> Result<ParseFuzzyOutput, ParseError> {
        let fuzzy_unit = match self.0.unit {
            Some(Month) => FuzzyUnit::Month,
            Some(Year) => FuzzyUnit::Year,
            _ => return self.parse().map(ParseFuzzyOutput::Duration),
        };

        if self.0.fract.is_some() {
            return Err(ParseError::InvalidInput(
                "Fraction only allowed together with seconds as time unit".to_owned(),
            ));
        }

        match self.0.whole {
            None if self.0.numeral.is_some() => {
                let Multiplier(coefficient, _) = self.0.numeral.unwrap() * self.0.multiplier;
                Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                    unit: fuzzy_unit,
                    value: if self.0.is_negative.unwrap_or_default() {
                        coefficient.saturating_neg()
                    } else {
                        coefficient
                    },
                }))
            }
            // We're here when we've encountered just a time unit
            None => Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                unit: fuzzy_unit,
                value: if self.0.is_negative.unwrap_or_default() ^ self.0.multiplier.is_negative() {
                    -1
                } else {
                    1
                },
            })),
            Some(whole) => {
                let is_negative =
                    self.0.is_negative.unwrap_or_default() ^ self.0.multiplier.is_negative();
                match Whole::parse(&self.0.input[whole.0..whole.1], None, None) {
                    Some(value) => match i64::try_from(value) {
                        Ok(value) if is_negative => Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                            unit: fuzzy_unit,
                            value: -value,
                        })),
                        Ok(value) => Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                            unit: fuzzy_unit,
                            value,
                        })),
                        Err(_) if is_negative => Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                            unit: fuzzy_unit,
                            value: i64::MIN,
                        })),
                        Err(_) => Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                            unit: fuzzy_unit,
                            value: i64::MAX,
                        })),
                    },
                    None if is_negative => Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                        unit: fuzzy_unit,
                        value: i64::MIN,
                    })),
                    None => Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                        unit: fuzzy_unit,
                        value: i64::MAX,
                    })),
                }
            }
        }
    }
}

/// The main gnu relative time parser
///
/// Note this parser can be created as const at compile time.
///
/// # Examples
///
/// ```rust
/// use fundu_gnu::{Duration, RelativeTimeParser};
///
/// const PARSER: RelativeTimeParser = RelativeTimeParser::new();
///
/// let parser = &PARSER;
/// assert_eq!(parser.parse("1hour"), Ok(Duration::positive(60 * 60, 0)));
/// assert_eq!(parser.parse("minute"), Ok(Duration::positive(60, 0)));
/// assert_eq!(
///     parser.parse("2 hours"),
///     Ok(Duration::positive(2 * 60 * 60, 0))
/// );
/// assert_eq!(parser.parse("second"), Ok(Duration::positive(1, 0)));
/// assert_eq!(parser.parse("-3minutes"), Ok(Duration::negative(3 * 60, 0)));
/// assert_eq!(
///     parser.parse("3 mins ago"),
///     Ok(Duration::negative(3 * 60, 0))
/// );
/// assert_eq!(
///     parser.parse("999sec +1day"),
///     Ok(Duration::positive(86_400 + 999, 0))
/// );
/// assert_eq!(
///     parser.parse("55secs500week"),
///     Ok(Duration::positive(55 + 500 * 7 * 24 * 60 * 60, 0))
/// );
/// assert_eq!(
///     parser.parse("300mins20secs 5hour"),
///     Ok(Duration::positive(300 * 60 + 20 + 5 * 60 * 60, 0))
/// );
/// assert_eq!(
///     parser.parse("123456789"),
///     Ok(Duration::positive(123_456_789, 0))
/// );
/// assert_eq!(
///     parser.parse("42fortnight"),
///     Ok(Duration::positive(42 * 2 * 7 * 24 * 60 * 60, 0))
/// );
/// assert_eq!(
///     parser.parse("yesterday"),
///     Ok(Duration::negative(24 * 60 * 60, 0))
/// );
/// assert_eq!(parser.parse("now"), Ok(Duration::positive(0, 0)));
/// assert_eq!(
///     parser.parse("today -10seconds"),
///     Ok(Duration::negative(10, 0))
/// );
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct RelativeTimeParser<'a> {
    raw: Parser<'a>,
}

impl RelativeTimeParser<'_> {
    /// Create a new `RelativeTimeParser`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{Duration, RelativeTimeParser};
    ///
    /// let parser = RelativeTimeParser::new();
    /// assert_eq!(
    ///     parser.parse("2hours"),
    ///     Ok(Duration::positive(2 * 60 * 60, 0))
    /// );
    /// assert_eq!(parser.parse("123"), Ok(Duration::positive(123, 0)));
    /// assert_eq!(
    ///     parser.parse("3min +10sec"),
    ///     Ok(Duration::positive(3 * 60 + 10, 0))
    /// );
    /// ```
    pub const fn new() -> Self {
        Self {
            raw: Parser::with_config(CONFIG),
        }
    }
    /// Parse the `source` string into a [`Duration`] relative to the date and time of `now`
    ///
    /// Any leading and trailing whitespace is ignored. The parser saturates at the maximum of
    /// [`Duration::MAX`].
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if an error during the parsing process occurred
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{Duration, RelativeTimeParser};
    ///
    /// let parser = RelativeTimeParser::new();
    /// assert_eq!(
    ///     parser.parse("2hours"),
    ///     Ok(Duration::positive(2 * 60 * 60, 0))
    /// );
    /// assert_eq!(parser.parse("12 seconds"), Ok(Duration::positive(12, 0)));
    /// assert_eq!(
    ///     parser.parse("123456789"),
    ///     Ok(Duration::positive(123_456_789, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse("yesterday"),
    ///     Ok(Duration::negative(24 * 60 * 60, 0))
    /// );
    /// ```
    #[inline]
    pub fn parse(&self, source: &str) -> Result<Duration, ParseError> {
        self.parse_with_date(source, None)
    }

    /// Parse the `source` string into a [`Duration`] relative to the optionally given `date`
    ///
    /// If the `date` is `None`, then the system time of `now` is assumed. Time units of `year` and
    /// `month` are parsed fuzzy since years and months are not all of equal length. Any leading and
    /// trailing whitespace is ignored. The parser saturates at the maximum of [`Duration::MAX`].
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if an error during the parsing process occurred or the calculation
    /// of the calculation of the given `date` plus the duration of the `source` string overflows.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{DateTime, Duration, RelativeTimeParser};
    ///
    /// let parser = RelativeTimeParser::new();
    /// assert_eq!(
    ///     parser.parse_with_date("2hours", None),
    ///     Ok(Duration::positive(2 * 60 * 60, 0))
    /// );
    ///
    /// let date_time = DateTime::from_gregorian_date_time(1970, 2, 1, 0, 0, 0, 0);
    /// assert_eq!(
    ///     parser.parse_with_date("+1month", Some(date_time)),
    ///     Ok(Duration::positive(28 * 86400, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse_with_date("+1year", Some(date_time)),
    ///     Ok(Duration::positive(365 * 86400, 0))
    /// );
    ///
    /// // 1972 is a leap year
    /// let date_time = DateTime::from_gregorian_date_time(1972, 2, 1, 0, 0, 0, 0);
    /// assert_eq!(
    ///     parser.parse_with_date("+1month", Some(date_time)),
    ///     Ok(Duration::positive(29 * 86400, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse_with_date("+1year", Some(date_time)),
    ///     Ok(Duration::positive(366 * 86400, 0))
    /// );
    /// ```
    pub fn parse_with_date(
        &self,
        source: &str,
        date: Option<DateTime>,
    ) -> Result<Duration, ParseError> {
        let (years, months, duration) = self.parse_fuzzy(source)?;
        if years == 0 && months == 0 {
            return Ok(duration);
        }

        // Delay the costly system call to get the utc time as late as possible
        let orig = date.unwrap_or_else(DateTime::now_utc);
        orig.checked_add_duration(&duration)
            .and_then(|date| {
                date.checked_add_gregorian(years, months, 0)
                    .and_then(|date| date.duration_since(orig))
            })
            .ok_or(ParseError::Overflow)
    }

    /// Parse the `source` string extracting `year` and `month` time units from the [`Duration`]
    ///
    /// Unlike [`RelativeTimeParser::parse`] and [`RelativeTimeParser::parse_with_date`] this method
    /// won't interpret the parsed `year` and `month` time units but simply returns the values
    /// parsed from the `source` string.
    ///
    /// The returned tuple (`years`, `months`, `Duration`) contains in the first component the
    /// amount parsed `years` as `i64`, in the second component the parsed `months` as `i64` and in
    /// the last component the rest of the parsed time units accumulated as [`Duration`].
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if an error during the parsing process occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{Duration, RelativeTimeParser};
    ///
    /// let parser = RelativeTimeParser::new();
    /// assert_eq!(
    ///     parser.parse_fuzzy("2hours"),
    ///     Ok((0, 0, Duration::positive(2 * 60 * 60, 0)))
    /// );
    /// assert_eq!(
    ///     parser.parse_fuzzy("2hours +123month -10years"),
    ///     Ok((-10, 123, Duration::positive(2 * 60 * 60, 0)))
    /// );
    /// ```
    #[allow(clippy::missing_panics_doc)]
    pub fn parse_fuzzy(&self, source: &str) -> Result<(i64, i64, Duration), ParseError> {
        let trimmed = trim_whitespace(source);

        let mut duration = Duration::ZERO;
        let mut years = 0i64;
        let mut months = 0i64;

        let mut parser = &mut ReprParserMultiple::new(trimmed);

        loop {
            let (duration_repr, maybe_parser) = parser.parse(
                &self.raw.config,
                &TIME_UNITS,
                Some(&TIME_KEYWORDS),
                Some(&NUMERALS),
            )?;

            match DurationReprParser(duration_repr).parse_fuzzy()? {
                ParseFuzzyOutput::Duration(parsed_duration) => {
                    duration = if duration.is_zero() {
                        parsed_duration
                    } else if parsed_duration.is_zero() {
                        duration
                    } else {
                        duration.saturating_add(parsed_duration)
                    }
                }
                ParseFuzzyOutput::FuzzyTime(fuzzy) => match fuzzy.unit {
                    FuzzyUnit::Month => months = months.saturating_add(fuzzy.value),
                    FuzzyUnit::Year => years = years.saturating_add(fuzzy.value),
                },
            }
            match maybe_parser {
                Some(p) => parser = p,
                None => break Ok((years, months, duration)),
            }
        }
    }
}

impl Default for RelativeTimeParser<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// This struct is used internally to hold the time units used by gnu
struct TimeUnits {}

impl TimeUnitsLike for TimeUnits {
    #[inline]
    fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        const SEC: [u64; 2] = [0x0000_0000_0063_6573, 0];
        const SECS: [u64; 2] = [0x0000_0000_7363_6573, 0];
        const SECOND: [u64; 2] = [0x0000_646E_6F63_6573, 0];
        const SECONDS: [u64; 2] = [0x0073_646E_6F63_6573, 0];
        const MIN: [u64; 2] = [0x0000_0000_006E_696D, 0];
        const MINS: [u64; 2] = [0x0000_0000_736E_696D, 0];
        const MINUTE: [u64; 2] = [0x0000_6574_756E_696D, 0];
        const MINUTES: [u64; 2] = [0x0073_6574_756E_696D, 0];
        const HOUR: [u64; 2] = [0x0000_0000_7275_6F68, 0];
        const HOURS: [u64; 2] = [0x0000_0073_7275_6F68, 0];
        const DAY: [u64; 2] = [0x0000_0000_0079_6164, 0];
        const DAYS: [u64; 2] = [0x0000_0000_7379_6164, 0];
        const WEEK: [u64; 2] = [0x0000_0000_6B65_6577, 0];
        const WEEKS: [u64; 2] = [0x0000_0073_6B65_6577, 0];
        const FORTNIGHT: [u64; 2] = [0x6867_696E_7472_6F66, 0x0000_0000_0000_0074];
        const FORTNIGHTS: [u64; 2] = [0x6867_696E_7472_6F66, 0x0000_0000_0000_7374];
        const MONTH: [u64; 2] = [0x0000_0068_746E_6F6D, 0];
        const MONTHS: [u64; 2] = [0x0000_7368_746E_6F6D, 0];
        const YEAR: [u64; 2] = [0x0000_0000_7261_6579, 0];
        const YEARS: [u64; 2] = [0x0000_0073_7261_6579, 0];

        match identifier.len() {
            3 => match to_lowercase_u64(identifier) {
                SEC => Some(SECOND_UNIT),
                MIN => Some(MINUTE_UNIT),
                DAY => Some(DAY_UNIT),
                _ => None,
            },
            4 => match to_lowercase_u64(identifier) {
                SECS => Some(SECOND_UNIT),
                MINS => Some(MINUTE_UNIT),
                DAYS => Some(DAY_UNIT),
                HOUR => Some(HOUR_UNIT),
                WEEK => Some(WEEK_UNIT),
                YEAR => Some(YEAR_UNIT),
                _ => None,
            },
            5 => match to_lowercase_u64(identifier) {
                HOURS => Some(HOUR_UNIT),
                WEEKS => Some(WEEK_UNIT),
                YEARS => Some(YEAR_UNIT),
                MONTH => Some(MONTH_UNIT),
                _ => None,
            },
            6 => match to_lowercase_u64(identifier) {
                SECOND => Some(SECOND_UNIT),
                MINUTE => Some(MINUTE_UNIT),
                MONTHS => Some(MONTH_UNIT),
                _ => None,
            },
            7 => match to_lowercase_u64(identifier) {
                SECONDS => Some(SECOND_UNIT),
                MINUTES => Some(MINUTE_UNIT),
                _ => None,
            },
            9 => (to_lowercase_u64(identifier) == FORTNIGHT).then_some(FORTNIGHT_UNIT),
            10 => (to_lowercase_u64(identifier) == FORTNIGHTS).then_some(FORTNIGHT_UNIT),
            _ => None,
        }
    }
}

/// This struct is used internally to hold the time keywords used by gnu
struct TimeKeywords {}

impl TimeUnitsLike for TimeKeywords {
    #[inline]
    fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        const NOW: [u64; 2] = [0x0000_0000_0077_6F6E, 0];
        const YESTERDAY: [u64; 2] = [0x6164_7265_7473_6579, 0x0000_0000_0000_0079];
        const TOMORROW: [u64; 2] = [0x776F_7272_6F6D_6F74, 0];
        const TODAY: [u64; 2] = [0x0000_0079_6164_6F74, 0];

        match identifier.len() {
            3 => (to_lowercase_u64(identifier) == NOW).then_some((TimeUnit::Day, Multiplier(0, 0))),
            5 => {
                (to_lowercase_u64(identifier) == TODAY).then_some((TimeUnit::Day, Multiplier(0, 0)))
            }
            8 => (to_lowercase_u64(identifier) == TOMORROW)
                .then_some((TimeUnit::Day, Multiplier(1, 0))),
            9 => (to_lowercase_u64(identifier) == YESTERDAY)
                .then_some((TimeUnit::Day, Multiplier(-1, 0))),
            _ => None,
        }
    }
}

struct Numerals {}

impl NumbersLike for Numerals {
    #[inline]
    fn get(&self, identifier: &str) -> Option<Multiplier> {
        const LAST: [u64; 2] = [0x0000_0000_7473_616C, 0];
        const THIS: [u64; 2] = [0x0000_0000_7369_6874, 0];
        const NEXT: [u64; 2] = [0x0000_0000_7478_656E, 0];
        const FIRST: [u64; 2] = [0x0000_0074_7372_6966, 0];
        const THIRD: [u64; 2] = [0x0000_0064_7269_6874, 0];
        const FOURTH: [u64; 2] = [0x0000_6874_7275_6F66, 0];
        const FIFTH: [u64; 2] = [0x0000_0068_7466_6966, 0];
        const SIXTH: [u64; 2] = [0x0000_0068_7478_6973, 0];
        const SEVENTH: [u64; 2] = [0x0068_746E_6576_6573, 0];
        const EIGHTH: [u64; 2] = [0x0000_6874_6867_6965, 0];
        const NINTH: [u64; 2] = [0x0000_0068_746E_696E, 0];
        const TENTH: [u64; 2] = [0x0000_0068_746E_6574, 0];
        const ELEVENTH: [u64; 2] = [0x6874_6E65_7665_6C65, 0];
        const TWELFTH: [u64; 2] = [0x0068_7466_6C65_7774, 0];

        match identifier.len() {
            4 => match to_lowercase_u64(identifier) {
                LAST => Some(Multiplier(-1, 0)),
                THIS => Some(Multiplier(0, 0)),
                NEXT => Some(Multiplier(1, 0)),
                _ => None,
            },
            5 => match to_lowercase_u64(identifier) {
                FIRST => Some(Multiplier(1, 0)),
                THIRD => Some(Multiplier(3, 0)),
                FIFTH => Some(Multiplier(5, 0)),
                SIXTH => Some(Multiplier(6, 0)),
                NINTH => Some(Multiplier(9, 0)),
                TENTH => Some(Multiplier(10, 0)),
                _ => None,
            },
            6 => match to_lowercase_u64(identifier) {
                FOURTH => Some(Multiplier(4, 0)),
                EIGHTH => Some(Multiplier(8, 0)),
                _ => None,
            },
            7 => match to_lowercase_u64(identifier) {
                SEVENTH => Some(Multiplier(7, 0)),
                TWELFTH => Some(Multiplier(12, 0)),
                _ => None,
            },
            8 => (ELEVENTH == to_lowercase_u64(identifier)).then_some(Multiplier(11, 0)),
            _ => None,
        }
    }
}

/// Parse the `source` string into a [`Duration`]
///
/// Any leading and trailing whitespace is ignored. The parser saturates at the maximum of
/// [`Duration::MAX`].
///
/// This method is equivalent to [`RelativeTimeParser::parse`]. See also the documentation of
/// [`RelativeTimeParser::parse`].
///
/// # Errors
///
/// Returns a [`ParseError`] if an error during the parsing process occurred
///
/// # Examples
///
/// ```rust
/// use fundu_gnu::{parse, Duration};
///
/// assert_eq!(parse("2hours"), Ok(Duration::positive(2 * 60 * 60, 0)));
/// assert_eq!(parse("12 seconds"), Ok(Duration::positive(12, 0)));
/// assert_eq!(parse("123456789"), Ok(Duration::positive(123_456_789, 0)));
/// assert_eq!(parse("yesterday"), Ok(Duration::negative(24 * 60 * 60, 0)));
/// ```
pub fn parse(source: &str) -> Result<Duration, ParseError> {
    PARSER.parse(source)
}

/// Parse the `source` string into a [`Duration`] relative to the optionally given `date`
///
/// If the `date` is `None`, then the system time of `now` is assumed. Time units of `year` and
/// `month` are parsed fuzzy since years and months are not all of equal length. Any leading and
/// trailing whitespace is ignored. The parser saturates at the maximum of [`Duration::MAX`].
///
/// This method is equivalent to [`RelativeTimeParser::parse_with_date`]. See also the documentation
/// of [`RelativeTimeParser::parse_with_date`].
///
/// # Errors
///
/// Returns a [`ParseError`] if an error during the parsing process occurred or the calculation
/// of the calculation of the given `date` plus the duration of the `source` string overflows.
///
/// # Examples
///
/// ```rust
/// use fundu_gnu::{parse_with_date, DateTime, Duration};
///
/// assert_eq!(
///     parse_with_date("2hours", None),
///     Ok(Duration::positive(2 * 60 * 60, 0))
/// );
///
/// let date_time = DateTime::from_gregorian_date_time(1970, 2, 1, 0, 0, 0, 0);
/// assert_eq!(
///     parse_with_date("+1month", Some(date_time)),
///     Ok(Duration::positive(28 * 86400, 0))
/// );
/// assert_eq!(
///     parse_with_date("+1year", Some(date_time)),
///     Ok(Duration::positive(365 * 86400, 0))
/// );
///
/// // 1972 is a leap year
/// let date_time = DateTime::from_gregorian_date_time(1972, 2, 1, 0, 0, 0, 0);
/// assert_eq!(
///     parse_with_date("+1month", Some(date_time)),
///     Ok(Duration::positive(29 * 86400, 0))
/// );
/// assert_eq!(
///     parse_with_date("+1year", Some(date_time)),
///     Ok(Duration::positive(366 * 86400, 0))
/// );
/// ```
pub fn parse_with_date(source: &str, date: Option<DateTime>) -> Result<Duration, ParseError> {
    PARSER.parse_with_date(source, date)
}

/// Parse the `source` string extracting `year` and `month` time units from the [`Duration`]
///
/// Unlike [`RelativeTimeParser::parse`] and [`RelativeTimeParser::parse_with_date`] this method
/// won't interpret the parsed `year` and `month` time units but simply returns the values
/// parsed from the `source` string.
///
/// The returned tuple (`years`, `months`, `Duration`) contains in the first component the
/// amount parsed `years` as `i64`, in the second component the parsed `months` as `i64` and in
/// the last component the rest of the parsed time units accumulated as [`Duration`].
///
/// This method is equivalent to [`RelativeTimeParser::parse_fuzzy`]. See also the documentation of
/// [`RelativeTimeParser::parse_fuzzy`].
///
/// # Errors
///
/// Returns a [`ParseError`] if an error during the parsing process occurred.
///
/// # Examples
///
/// ```rust
/// use fundu_gnu::{parse_fuzzy, Duration};
///
/// assert_eq!(
///     parse_fuzzy("2hours"),
///     Ok((0, 0, Duration::positive(2 * 60 * 60, 0)))
/// );
/// assert_eq!(
///     parse_fuzzy("2hours +123month -10years"),
///     Ok((-10, 123, Duration::positive(2 * 60 * 60, 0)))
/// );
/// ```
pub fn parse_fuzzy(source: &str) -> Result<(i64, i64, Duration), ParseError> {
    PARSER.parse_fuzzy(source)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_relative_time_parser_new() {
        assert_eq!(RelativeTimeParser::new(), RelativeTimeParser::default());
    }

    #[test]
    fn test_time_units_is_empty_returns_false() {
        assert!(!TimeUnits {}.is_empty());
    }

    #[test]
    fn test_keywords_is_empty_returns_false() {
        assert!(!TimeKeywords {}.is_empty());
    }
}
