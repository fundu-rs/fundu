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
//! seconds time units allow a fraction (like in `"1.123456 secs"`)
//! - Multiple durations like `"1sec 2min"` or `"1week2secs"` in the source string accumulate
//! - Time units without a number (like in `"second"`) are allowed and a value of `1` is assumed.
//! - The parsed duration represents the value exactly (without rounding errors as would occur in
//! floating point calculations) as it is specified in the source string.
//! - The maximum supported duration (`Duration::MAX`) has `u64::MAX` seconds
//! (`18_446_744_073_709_551_615`) and `999_999_999` nano seconds
//! - parsed durations larger than the maximum duration saturate at the maximum duration
//! - Negative durations like `"-1min"` or `"1 week ago"` are allowed
//! - Any leading, trailing whitespace or whitespace between the number and the time unit (like in
//! `"1 \n sec"`) and multiple durations (like in `"1week \n 2minutes"`) is ignored and follows the
//! posix definition of whitespace which is:
//!   - Space (`' '`)
//!   - Horizontal Tab (`'\x09'`)
//!   - Line Feed (`'\x0A'`)
//!   - Vertical Tab (`'\x0B'`)
//!   - Form Feed (`'\x0C'`)
//!   - Carriage Return (`'\x0D'`)
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

use std::time::Duration as StdDuration;

pub use datetime::{DateTime, JulianDay};
use fundu_core::config::{Config, ConfigBuilder, Delimiter};
pub use fundu_core::error::{ParseError, TryFromDurationError};
use fundu_core::parse::{
    DurationRepr, Fract, Parser, ReprParserMultiple, ReprParserTemplate, Whole, ATTOS_PER_NANO,
    ATTOS_PER_SEC,
};
use fundu_core::time::TimeUnit::*;
pub use fundu_core::time::{Duration, SaturatingInto};
use fundu_core::time::{Multiplier, TimeUnit, TimeUnitsLike};
#[cfg(test)]
pub use rstest_reuse;
use util::trim_whitespace;

// whitespace definition of: b' ', b'\x09', b'\x0A', b'\x0B', b'\x0C', b'\x0D'
const DELIMITER: Delimiter = |byte| byte == b' ' || byte.wrapping_sub(9) < 5;

const CONFIG: Config = ConfigBuilder::new()
    .allow_delimiter(DELIMITER)
    .allow_ago(DELIMITER)
    .disable_exponent()
    .disable_infinity()
    .allow_negative()
    .number_is_optional()
    .parse_multiple(DELIMITER, None)
    .build();

const TIME_UNITS: TimeUnits = TimeUnits {};
const TIME_KEYWORDS: TimeKeywords = TimeKeywords {};

const SECOND: (TimeUnit, Multiplier) = (Second, Multiplier(1, 0));
const MINUTE: (TimeUnit, Multiplier) = (Minute, Multiplier(1, 0));
const HOUR: (TimeUnit, Multiplier) = (Hour, Multiplier(1, 0));
const DAY: (TimeUnit, Multiplier) = (Day, Multiplier(1, 0));
const WEEK: (TimeUnit, Multiplier) = (Week, Multiplier(1, 0));
const FORTNIGHT: (TimeUnit, Multiplier) = (Week, Multiplier(2, 0));
const MONTH: (TimeUnit, Multiplier) = (Month, Multiplier(1, 0));
const YEAR: (TimeUnit, Multiplier) = (Year, Multiplier(1, 0));

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

impl<'a> DurationReprParser<'a> {
    fn parse(&mut self) -> Result<Duration, ParseError> {
        let (whole, fract) = match (self.0.whole.take(), self.0.fract.take()) {
            (None, None) if self.0.number_is_optional => {
                let Multiplier(coefficient, _) = self.0.unit.multiplier() * self.0.multiplier;
                let duration_is_negative = self.0.is_negative ^ coefficient.is_negative();
                return Ok(Self::calculate_duration(
                    duration_is_negative,
                    1,
                    0,
                    coefficient,
                ));
            }
            (None, None) => unreachable!(), // cov:excl-line
            (None, Some(fract)) if self.0.unit == TimeUnit::Second => {
                (Whole(fract.0, fract.0), fract)
            }
            (Some(whole), None) => {
                let fract_start_and_end = whole.1;
                (whole, Fract(fract_start_and_end, fract_start_and_end))
            }
            (Some(whole), Some(fract)) if self.0.unit == TimeUnit::Second => (whole, fract),
            (Some(_) | None, Some(_)) => {
                return Err(ParseError::InvalidInput(
                    "Fraction only allowed together with seconds as time unit".to_owned(),
                ));
            }
        };

        // Panic on overflow during the multiplication of the multipliers or adding the exponents
        let Multiplier(coefficient, _) = self.0.unit.multiplier() * self.0.multiplier;
        let duration_is_negative = self.0.is_negative ^ coefficient.is_negative();

        let digits = self.0.input;
        let result = Whole::parse(&digits[whole.0..whole.1], None, None)
            .map(|s| (s, Fract::parse(&digits[fract.0..fract.1], None, None)));

        // interpret the result and a seconds overflow as maximum (minimum) `Duration`
        let (seconds, attos) = match result {
            Ok(value) => value,
            Err(ParseError::Overflow) if duration_is_negative => {
                return Ok(Duration::MIN);
            }
            Err(ParseError::Overflow) => {
                return Ok(Duration::MAX);
            }
            // only ParseError::Overflow is returned by `Seconds::parse`
            Err(_) => unreachable!(), // cov:excl-line
        };

        Ok(Self::calculate_duration(
            duration_is_negative,
            seconds,
            attos,
            coefficient,
        ))
    }

    fn parse_fuzzy(&mut self) -> Result<ParseFuzzyOutput, ParseError> {
        let fuzzy_unit = match self.0.unit {
            Month => FuzzyUnit::Month,
            Year => FuzzyUnit::Year,
            _ => return self.parse().map(ParseFuzzyOutput::Duration),
        };

        if self.0.fract.is_some() {
            return Err(ParseError::InvalidInput(
                "Fraction only allowed together with seconds as time unit".to_owned(),
            ));
        }

        let whole = match self.0.whole.take() {
            Some(whole) => whole,
            None if self.0.number_is_optional => {
                return Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                    unit: fuzzy_unit,
                    value: if self.0.is_negative { -1 } else { 1 },
                }));
            }
            None => unreachable!(), // cov:excl-line
        };

        let result = Whole::parse(&self.0.input[whole.0..whole.1], None, None);
        // interpret the result and a years or month overflow as maximum (minimum) `Duration`
        let value = match result {
            Ok(value) => value,
            Err(ParseError::Overflow) if self.0.is_negative => {
                return Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                    unit: fuzzy_unit,
                    value: i64::MIN,
                }));
            }
            Err(ParseError::Overflow) => {
                return Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
                    unit: fuzzy_unit,
                    value: i64::MAX,
                }));
            }
            // only ParseError::Overflow is returned by `Seconds::parse`
            Err(_) => unreachable!(), // cov:excl-line
        };

        let value = i64::try_from(value).unwrap_or(i64::MAX);
        Ok(ParseFuzzyOutput::FuzzyTime(FuzzyTime {
            unit: fuzzy_unit,
            value: if self.0.is_negative { -value } else { value },
        }))
    }

    fn calculate_duration(
        is_negative: bool,
        seconds: u64,
        attos: u64,
        coefficient: i64,
    ) -> Duration {
        if seconds == 0 && attos == 0 {
            Duration::ZERO
        } else if coefficient == 1 || coefficient == -1 {
            Duration::from_std(
                is_negative,
                StdDuration::new(seconds, (attos / ATTOS_PER_NANO).try_into().unwrap()),
            )
        } else {
            let unsigned_coefficient = coefficient.unsigned_abs();

            let attos = u128::from(attos) * u128::from(unsigned_coefficient);
            match seconds.checked_mul(unsigned_coefficient).and_then(|s| {
                s.checked_add((attos / u128::from(ATTOS_PER_SEC)).try_into().unwrap())
            }) {
                Some(s) => Duration::from_std(
                    is_negative,
                    StdDuration::new(
                        s,
                        ((attos / u128::from(ATTOS_PER_NANO)) % 1_000_000_000) as u32,
                    ),
                ),
                None if is_negative => Duration::MIN,
                None => Duration::MAX,
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

impl<'a> RelativeTimeParser<'a> {
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

        // the unwraps are safe here because both config values are defined
        let mut parser = &mut ReprParserMultiple::new(
            trimmed,
            self.raw.config.delimiter_multiple.unwrap(),
            self.raw.config.conjunctions.unwrap_or_default(),
        );

        loop {
            let (duration_repr, maybe_parser) =
                parser.parse(&self.raw.config, &TIME_UNITS, Some(&TIME_KEYWORDS))?;

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

impl<'a> Default for RelativeTimeParser<'a> {
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
        match identifier {
            "sec" | "secs" | "second" | "seconds" => Some(SECOND),
            "min" | "mins" | "minute" | "minutes" => Some(MINUTE),
            "hour" | "hours" => Some(HOUR),
            "day" | "days" => Some(DAY),
            "week" | "weeks" => Some(WEEK),
            "fortnight" | "fortnights" => Some(FORTNIGHT),
            "month" | "months" => Some(MONTH),
            "year" | "years" => Some(YEAR),
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
        match identifier {
            "yesterday" => Some((TimeUnit::Day, Multiplier(-1, 0))),
            "tomorrow" => Some((TimeUnit::Day, Multiplier(1, 0))),
            "now" | "today" => Some((TimeUnit::Day, Multiplier(0, 0))),
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
