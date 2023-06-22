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
//! `"1year 12months"`| `Duration::positive(63_115_200, 0)` |
//! `"-3minutes"`| `Duration::negative(3 * 60, 0)` |
//! `"3 mins ago"`| `Duration::negative(3 * 60, 0)` |
//! `"999sec +1day"`| `Duration::positive(86_400 + 999, 0)` |
//! `"55secs500week"`| `Duration::positive(55 + 500 * 604_800, 0)` |
//! `"123456789"`| `Duration::positive(123_456_789, 0)` |
//! `"42fortnight"`| `Duration::positive(42 * 2 * 604_800, 0)` |
//! `"yesterday"`| `Duration::negative(24 * 60 * 60, 0)` |
//! `"now"`| `Duration::positive(0, 0)` |
//! `"today -10seconds"`| `Duration::negative(10, 0)` |
//! `"1000000000000000000000000000000000000years"`| `Duration::MAX` |
//!
//! Note that `fundu` parses into its own [`Duration`] which is a superset of other `Durations` like
//! [`std::time::Duration`], [`chrono::Duration`] and [`time::Duration`]. See the
//! [documentation](https://docs.rs/fundu/latest/fundu/index.html#fundus-duration) how to easily
//! handle the conversion between these durations.
//!
//! # The Format
//!
//! Supported time units:
//!
//! - `seconds`, `second`, `secs`, `sec`
//! - `minutes`, `minute`, `mins`, `min`
//! - `hours`, `hour`
//! - `days`, `day`
//! - `weeks`, `week`
//! - `fortnights`, `fortnight` (2 weeks)
//! - `months`, `month` (defined as `30.44` days or a `1/12` year)
//! - `years`, `year` (defined as `365.25` days)
//!
//! The special keywords `yesterday` worth `-1 day`, `tomorrow` worth `+1 day`, `today` and `now`
//! each worth a zero duration are allowed, too. These keywords count as a full duration and don't
//! accept a number, time unit or the `ago` time unit suffix.
//!
//! Summary of the rest of the format:
//!
//! - Only numbers like `"123 days"` without fraction (like in `"1.2 days"`) and without exponent
//!   (like
//! `"3e9 days"`) are allowed
//! - Multiple durations like `"1sec 2min"` or `"1week2secs"` in the source string accumulate
//! - Time units without a number (like in `"second"`) are allowed and a value of `1` is assumed.
//! - The parsed duration represents the value exactly (without rounding errors as would occur in
//! floating point calculations) as it is specified in the source string.
//! - The maximum supported duration (`Duration::MAX`) has `u64::MAX` seconds
//! (`18_446_744_073_709_551_615`) and `999_999_999` nano seconds
//! - parsed durations larger than the maximum duration (like `"100000000000000years"`) saturate at
//! the maximum duration
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
//! use fundu::Duration;
//! use fundu_gnu::RelativeTimeParser;
//!
//! let parser = RelativeTimeParser::new();
//! assert_eq!(parser.parse("1hour"), Ok(Duration::positive(60 * 60, 0)));
//! assert_eq!(parser.parse("minute"), Ok(Duration::positive(60, 0)));
//! assert_eq!(
//!     parser.parse("2 hours"),
//!     Ok(Duration::positive(2 * 60 * 60, 0))
//! );
//! assert_eq!(parser.parse("second"), Ok(Duration::positive(1, 0)));
//! assert_eq!(
//!     parser.parse("1year 12months"),
//!     Ok(Duration::positive(63_115_200, 0))
//! );
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
//! assert_eq!(
//!     parser.parse("1000000000000000000000000000000000000years"),
//!     Ok(Duration::MAX)
//! );
//! ```
//!
//! Or use the global method [`parse`] which does the same without the need to create a parser
//! struct.
//!
//! ```rust
//! use fundu::Duration;
//! use fundu_gnu::parse;
//!
//! assert_eq!(parse("123 sec"), Ok(Duration::positive(123, 0)));
//! assert_eq!(parse("1sec3min"), Ok(Duration::positive(1 + 3 * 60, 0)));
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

use fundu::TimeUnit::*;
use fundu::{
    Config, ConfigBuilder, Delimiter, Duration, Multiplier, ParseError, Parser, TimeUnit,
    TimeUnitsLike,
};

// whitespace definition of: b' ', b'\x09', b'\x0A', b'\x0B', b'\x0C', b'\x0D'
const DELIMITER: Delimiter = |byte| byte == b' ' || byte.wrapping_sub(9) < 5;

const CONFIG: Config = ConfigBuilder::new()
    .allow_delimiter(DELIMITER)
    .allow_ago(DELIMITER)
    .disable_exponent()
    .disable_infinity()
    .disable_fraction()
    .number_is_optional()
    .allow_negative()
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

/// The main gnu relative time parser
///
/// Note this parser can be created as const at compile time.
///
/// # Examples
///
/// ```rust
/// use fundu::Duration;
/// use fundu_gnu::RelativeTimeParser;
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
/// assert_eq!(
///     parser.parse("1year 12months"),
///     Ok(Duration::positive(63_115_200, 0))
/// );
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
/// assert_eq!(
///     parser.parse("1000000000000000000000000000000000000years"),
///     Ok(Duration::MAX)
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
    /// use fundu::Duration;
    /// use fundu_gnu::RelativeTimeParser;
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
    /// Parse the `source` string into a [`Duration`]
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
    /// use fundu::Duration;
    /// use fundu_gnu::RelativeTimeParser;
    ///
    /// let parser = RelativeTimeParser::new();
    /// assert_eq!(
    ///     parser.parse("2hours"),
    ///     Ok(Duration::positive(2 * 60 * 60, 0))
    /// );
    /// assert_eq!(parser.parse("12 seconds"), Ok(Duration::positive(12, 0)));
    /// assert_eq!(
    ///     parser.parse("1year 12months"),
    ///     Ok(Duration::positive(63_115_200, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse("123456789"),
    ///     Ok(Duration::positive(123_456_789, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse("100000000000000000000000000000years"),
    ///     Ok(Duration::MAX)
    /// );
    /// assert_eq!(
    ///     parser.parse("yesterday"),
    ///     Ok(Duration::negative(24 * 60 * 60, 0))
    /// );
    /// ```
    pub fn parse(&self, source: &str) -> Result<Duration, ParseError> {
        let trimmed = trim_whitespace(source);
        self.raw.parse(trimmed, &TIME_UNITS, Some(&TIME_KEYWORDS))
    }
}

impl<'a> Default for RelativeTimeParser<'a> {
    fn default() -> Self {
        Self::new()
    }
}

/// This struct is used internally to hold the time units used by gnu
pub struct TimeUnits {}

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
pub struct TimeKeywords {}

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
/// # Errors
///
/// Returns a [`ParseError`] if an error during the parsing process occurred
///
/// # Examples
///
/// ```rust
/// use fundu::Duration;
/// use fundu_gnu::parse;
///
/// assert_eq!(parse("2hours"), Ok(Duration::positive(2 * 60 * 60, 0)));
/// assert_eq!(parse("12 seconds"), Ok(Duration::positive(12, 0)));
/// assert_eq!(
///     parse("1year 12months"),
///     Ok(Duration::positive(63_115_200, 0))
/// );
/// assert_eq!(parse("123456789"), Ok(Duration::positive(123_456_789, 0)));
/// assert_eq!(
///     parse("100000000000000000000000000000years"),
///     Ok(Duration::MAX)
/// );
/// assert_eq!(parse("yesterday"), Ok(Duration::negative(24 * 60 * 60, 0)));
/// ```
pub fn parse(source: &str) -> Result<Duration, ParseError> {
    PARSER.parse(source)
}

// This is a faster alternative to str::trim_matches. We're exploiting that we're using the posix
// definition of whitespace which only contains ascii characters as whitespace
fn trim_whitespace(source: &str) -> &str {
    let mut bytes = source.as_bytes();
    while let Some((byte, remainder)) = bytes.split_first() {
        if byte == &b' ' || byte.wrapping_sub(9) < 5 {
            bytes = remainder;
        } else {
            break;
        }
    }
    while let Some((byte, remainder)) = bytes.split_last() {
        if byte == &b' ' || byte.wrapping_sub(9) < 5 {
            bytes = remainder;
        } else {
            break;
        }
    }
    // SAFETY: We've trimmed only ascii characters and therefore valid utf-8
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

#[cfg(test)]
mod tests {}
