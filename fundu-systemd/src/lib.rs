// spell-checker: ignore econd inute onths nute nths econds inutes

//! A simple to use, fast and accurate systemd time span parser fully compatible with the
//! [systemd time span format](https://www.freedesktop.org/software/systemd/man/systemd.time.html)
//!
//! `fundu-systemd` can parse rust strings like
//!
//! | `&str` | Duration |
//! | -- | -- |
//! | `"2 h"` | `Duration::positive(2 * 60 * 60, 0)` |
//! | `"2hours"` |`Duration::positive(2 * 60 * 60, 0)` |
//! | `"second"` |`Duration::positive(1, 0)` |
//! | `"48hr"` |`Duration::positive(48 * 60 * 60, 0)` |
//! | `"12.3 seconds"` |`Duration::positive(12, 300_000_000)` |
//! | `"1y 12month"` | `Duration::positive(63_115_200, 0)` |
//! | `"999us +1d"` |`Duration::positive(86_400, 999_000)` |
//! | `"55s500ms"` | `Duration::positive(55, 500_000_000)` |
//! | `"300ms20s 5day"` |`Duration::positive(20 + 5 * 60 * 60 * 24, 300_000_000)` |
//! | `"123456789"` |`Duration::positive(123_456_789, 0)` (Default: Second) |
//! | `"100"` |`Duration::positive(0, 100_000)` (when default is set to `MicroSecond`) |
//! | `"infinity"` | variable: the maximum duration which is currently in use (see below) |
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
//! - `nsec`, `ns` (can be switched on, per default these are not included)
//! - `usec`, `us`, `µs`
//! - `msec,` `ms`
//! - `seconds`, `second`, `sec`, `s`
//! - `minutes`, `minute`, `min`, `m`
//! - `hours`, `hour`, `hr`, `h`
//! - `days`, `day`, `d`
//! - `weeks`, `week`, `w`
//! - `months`, `month`, `M` (defined as `30.44` days or a `1/12` year)
//! - `years`, `year`, `y` (defined as `365.25` days)
//!
//! Summary of the rest of the format:
//!
//! - Only numbers like `"123 days"` or with fraction `"1.2 days"` but without exponent (like `"3e9
//! days"`) are allowed
//! - For numbers without a time unit (like `"1234"`) the default time unit is usually `second` but
//!   can
//! be changed since in some case systemd uses a different granularity.
//! - Time units without a number (like in `"second"`) are allowed and a value of `1` is assumed.
//! - The parsed duration represents the value exactly (without rounding errors as would occur in
//! floating point calculations) as it is specified in the source string (just like systemd).
//! - The maximum supported duration (`Duration::MAX`) has `u64::MAX` seconds
//! (`18_446_744_073_709_551_615`) and `999_999_999` nano seconds. However, systemd uses `u64::MAX`
//! micro seconds as maximum duration when parsing without nanos and `u64::MAX` nano seconds when
//! parsing with nanos. `fundu-systemd` provides the `parse` and `parse_nanos` functions to reflect
//! that. If you don't like the maximum duration of `systemd` it's still possible via
//! `parse_with_max` and `parse_nanos_with_max` to adjust this limit to a duration ranging from
//! `Duration::ZERO` to `Duration::MAX`.
//! - The special value `"infinity"` evaluates to the maximum duration. Note the maximum duration
//! depends on whether parsing with nano seconds or without. If the maximum duration is manually set
//! to a different value then it evaluates to that maximum duration.
//! - parsed durations larger than the maximum duration (like `"100000000000000years"`)
//! saturate at the maximum duration
//! - Negative durations are not allowed, also no intermediate negative durations like in `"5day
//!   -1ms"`
//! although the final duration would not be negative.
//! - Any leading, trailing whitespace or whitespace between the number and the time unit (like in
//!   `"1
//! \n sec"`) and multiple durations (like in `"1week \n 2minutes"`) is ignored and follows the
//! posix definition of whitespace which is:
//!     - Space (`' '`)
//!     - Horizontal Tab (`'\x09'`)
//!     - Line Feed (`'\x0A'`)
//!     - Vertical Tab (`'\x0B'`)
//!     - Form Feed (`'\x0C'`)
//!     - Carriage Return (`'\x0D'`)
//!
//! Please see also the systemd
//! [documentation](https://www.freedesktop.org/software/systemd/man/systemd.time.html) for a
//! description of their format.
//!
//! # Examples
//!
//! A re-usable parser providing different parse methods
//!
//! ```rust
//! use fundu::Duration;
//! use fundu_systemd::{TimeSpanParser, SYSTEMD_MAX_MICRO_DURATION, SYSTEMD_MAX_NANOS_DURATION};
//!
//! const PARSER: TimeSpanParser = TimeSpanParser::new();
//!
//! let parser = &PARSER;
//! assert_eq!(parser.parse("2h"), Ok(Duration::positive(2 * 60 * 60, 0)));
//! assert_eq!(parser.parse("second"), Ok(Duration::positive(1, 0)));
//! assert_eq!(
//!     parser.parse("48hr"),
//!     Ok(Duration::positive(48 * 60 * 60, 0))
//! );
//! assert_eq!(
//!     parser.parse("12.3 seconds"),
//!     Ok(Duration::positive(12, 300_000_000))
//! );
//! assert_eq!(
//!     parser.parse("300ms20s 5day"),
//!     Ok(Duration::positive(20 + 5 * 60 * 60 * 24, 300_000_000))
//! );
//! assert_eq!(
//!     parser.parse("123456789"),
//!     Ok(Duration::positive(123_456_789, 0))
//! );
//! assert_eq!(parser.parse("infinity"), Ok(SYSTEMD_MAX_MICRO_DURATION));
//!
//! // Or parsing nano seconds
//! assert_eq!(
//!     parser.parse_nanos("7809 nsec"),
//!     Ok(Duration::positive(0, 7809))
//! );
//! assert_eq!(
//!     parser.parse_nanos("infinity"),
//!     Ok(SYSTEMD_MAX_NANOS_DURATION)
//! );
//! ```
//!
//! Change the default unit to something different than `Second`
//! ```rust
//! use fundu::{Duration, TimeUnit};
//! use fundu_systemd::TimeSpanParser;
//!
//! let parser = TimeSpanParser::with_default_unit(TimeUnit::MicroSecond);
//! assert_eq!(parser.parse("100"), Ok(Duration::positive(0, 100_000)));
//!
//! let mut parser = TimeSpanParser::new();
//! parser.set_default_unit(TimeUnit::MicroSecond);
//!
//! assert_eq!(parser.parse("100"), Ok(Duration::positive(0, 100_000)));
//! ```
//!
//! Or use one of the global methods [`parse`], [`parse_nanos`].
//!
//! ```rust
//! use fundu::{Duration, ParseError};
//! use fundu_systemd::{
//!     parse, parse_nanos, SYSTEMD_MAX_MICRO_DURATION, SYSTEMD_MAX_NANOS_DURATION,
//! };
//!
//! assert_eq!(parse("123 sec", None, None), Ok(Duration::positive(123, 0)));
//!
//! // This is an error with `parse` because the nano seconds are excluded
//! assert_eq!(
//!     parse("123 nsec", None, None),
//!     Err(ParseError::InvalidInput("nsec".to_string()))
//! );
//!
//! // Use `parse_nanos` if the nano second time units should be included
//! assert_eq!(
//!     parse_nanos("123 nsec", None, None),
//!     Ok(Duration::positive(0, 123))
//! );
//!
//! // The maximum duration differs depending on the method in use
//! assert_eq!(
//!     parse("infinity", None, None),
//!     Ok(SYSTEMD_MAX_MICRO_DURATION)
//! );
//! assert_eq!(
//!     parse_nanos("infinity", None, None),
//!     Ok(SYSTEMD_MAX_NANOS_DURATION)
//! );
//!
//! // But can be easily changed
//! assert_eq!(
//!     parse_nanos("infinity", None, Some(Duration::MAX)),
//!     Ok(Duration::MAX)
//! );
//! ```
//!
//! For further details see [`parse`], [`parse_nanos`] or the documentation of [`TimeSpanParser`]
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
    .allow_time_unit_delimiter()
    .disable_exponent()
    .disable_infinity()
    .number_is_optional()
    .parse_multiple(None)
    .inner_delimiter(DELIMITER)
    .outer_delimiter(DELIMITER)
    .build();

const TIME_UNITS_WITH_NANOS: TimeUnitsWithNanos = TimeUnitsWithNanos {};
const TIME_UNITS: TimeUnits = TimeUnits {};

const NANO_SECOND: (TimeUnit, Multiplier) = (NanoSecond, Multiplier(1, 0));
const MICRO_SECOND: (TimeUnit, Multiplier) = (MicroSecond, Multiplier(1, 0));
const MILLI_SECOND: (TimeUnit, Multiplier) = (MilliSecond, Multiplier(1, 0));
const SECOND: (TimeUnit, Multiplier) = (Second, Multiplier(1, 0));
const MINUTE: (TimeUnit, Multiplier) = (Minute, Multiplier(1, 0));
const HOUR: (TimeUnit, Multiplier) = (Hour, Multiplier(1, 0));
const DAY: (TimeUnit, Multiplier) = (Day, Multiplier(1, 0));
const WEEK: (TimeUnit, Multiplier) = (Week, Multiplier(1, 0));
const MONTH: (TimeUnit, Multiplier) = (Month, Multiplier(1, 0));
const YEAR: (TimeUnit, Multiplier) = (Year, Multiplier(1, 0));

const PARSER: TimeSpanParser<'static> = TimeSpanParser::new();

/// The maximum duration used when parsing with micro seconds precision
pub const SYSTEMD_MAX_MICRO_DURATION: Duration =
    Duration::positive(u64::MAX / 1_000_000, (u64::MAX % 1_000_000) as u32 * 1000);

/// The maximum duration used when parsing with nano seconds precision
pub const SYSTEMD_MAX_NANOS_DURATION: Duration =
    Duration::positive(u64::MAX / 1_000_000_000, (u64::MAX % 1_000_000_000) as u32);

/// The main systemd time span parser
///
/// Note this parser can be created as const at compile time.
///
/// # Examples
///
/// ```rust
/// use fundu::Duration;
/// use fundu_systemd::{TimeSpanParser, SYSTEMD_MAX_MICRO_DURATION};
///
/// const PARSER: TimeSpanParser = TimeSpanParser::new();
///
/// let parser = &PARSER;
/// assert_eq!(parser.parse("2h"), Ok(Duration::positive(2 * 60 * 60, 0)));
/// assert_eq!(
///     parser.parse("2hours"),
///     Ok(Duration::positive(2 * 60 * 60, 0))
/// );
/// assert_eq!(parser.parse("second"), Ok(Duration::positive(1, 0)));
/// assert_eq!(
///     parser.parse("48hr"),
///     Ok(Duration::positive(48 * 60 * 60, 0))
/// );
/// assert_eq!(
///     parser.parse("12.3 seconds"),
///     Ok(Duration::positive(12, 300_000_000))
/// );
/// assert_eq!(
///     parser.parse("1y 12month"),
///     Ok(Duration::positive(63_115_200, 0))
/// );
/// assert_eq!(
///     parser.parse("999us +1d"),
///     Ok(Duration::positive(86_400, 999_000))
/// );
/// assert_eq!(
///     parser.parse("55s500ms"),
///     Ok(Duration::positive(55, 500_000_000))
/// );
/// assert_eq!(
///     parser.parse("300ms20s 5day"),
///     Ok(Duration::positive(20 + 5 * 60 * 60 * 24, 300_000_000))
/// );
/// assert_eq!(
///     parser.parse("123456789"),
///     Ok(Duration::positive(123_456_789, 0))
/// );
/// assert_eq!(parser.parse("infinity"), Ok(SYSTEMD_MAX_MICRO_DURATION));
/// ```
///
/// It's possible to change the default unit to something different than `Second` either during the
/// initialization with [`TimeSpanParser::with_default_unit`] or at runtime with
/// [`TimeSpanParser::set_default_unit`]
///
/// ```rust
/// use fundu::{Duration, TimeUnit};
/// use fundu_systemd::TimeSpanParser;
///
/// let parser = TimeSpanParser::with_default_unit(TimeUnit::MicroSecond);
/// assert_eq!(parser.parse("100"), Ok(Duration::positive(0, 100_000)));
///
/// let mut parser = TimeSpanParser::new();
/// parser.set_default_unit(TimeUnit::MicroSecond);
///
/// assert_eq!(parser.parse("100"), Ok(Duration::positive(0, 100_000)));
/// ```
#[derive(Debug, Eq, PartialEq)]
pub struct TimeSpanParser<'a> {
    raw: Parser<'a>,
}

impl<'a> TimeSpanParser<'a> {
    /// Create a new `TimeSpanParser` with [`TimeUnit::Second`] as default unit
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    /// use fundu_systemd::TimeSpanParser;
    ///
    /// let parser = TimeSpanParser::new();
    /// assert_eq!(parser.parse("2h"), Ok(Duration::positive(2 * 60 * 60, 0)));
    /// assert_eq!(parser.parse("123"), Ok(Duration::positive(123, 0)));
    /// assert_eq!(
    ///     parser.parse("3us +10sec"),
    ///     Ok(Duration::positive(10, 3_000))
    /// );
    /// ```
    pub const fn new() -> Self {
        Self {
            raw: Parser::with_config(CONFIG),
        }
    }

    /// Create a new `TimeSpanParser` with the specified [`TimeUnit`] as default
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{Duration, TimeUnit};
    /// use fundu_systemd::TimeSpanParser;
    ///
    /// let parser = TimeSpanParser::with_default_unit(TimeUnit::MicroSecond);
    /// assert_eq!(parser.parse("123"), Ok(Duration::positive(0, 123_000)));
    /// assert_eq!(
    ///     parser.parse("3us +10sec"),
    ///     Ok(Duration::positive(10, 3_000))
    /// );
    /// ```
    pub const fn with_default_unit(time_unit: TimeUnit) -> Self {
        let mut config = CONFIG;
        config.default_unit = time_unit;
        Self {
            raw: Parser::with_config(config),
        }
    }

    fn parse_infinity(source: &str, max: Duration) -> Option<Duration> {
        (source == "infinity").then_some(max)
    }

    /// Parse the `source` string into a [`Duration`]
    ///
    /// This method does not include the time units for nano seconds unlike the
    /// [`TimeSpanParser::parse_nanos`] method. The parser saturates at the maximum [`Duration`] of
    /// `u64::MAX` micro seconds. If you need a different maximum use the
    /// [`TimeSpanParser::parse_with_max`] method.
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if an error during the parsing process occurred
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    /// use fundu_systemd::{TimeSpanParser, SYSTEMD_MAX_MICRO_DURATION};
    ///
    /// let parser = TimeSpanParser::new();
    /// assert_eq!(
    ///     parser.parse("2hours"),
    ///     Ok(Duration::positive(2 * 60 * 60, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse("12.3 seconds"),
    ///     Ok(Duration::positive(12, 300_000_000))
    /// );
    /// assert_eq!(
    ///     parser.parse("100000000000000000000000000000years"),
    ///     Ok(SYSTEMD_MAX_MICRO_DURATION)
    /// );
    /// assert_eq!(
    ///     parser.parse("1y 12month"),
    ///     Ok(Duration::positive(63_115_200, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse("123456789"),
    ///     Ok(Duration::positive(123_456_789, 0))
    /// );
    /// assert_eq!(parser.parse("infinity"), Ok(SYSTEMD_MAX_MICRO_DURATION));
    /// ```
    pub fn parse(&self, source: &str) -> Result<Duration, ParseError> {
        self.parse_with_max(source, SYSTEMD_MAX_MICRO_DURATION)
    }

    /// Parse the `source` string into a [`Duration`] saturating at the given `max` [`Duration`]
    ///
    /// This method does not include the time units for nano seconds unlike the
    /// [`TimeSpanParser::parse_nanos_with_max`] method
    ///
    /// # Panics
    ///
    /// This method panics if `max` is a a negative [`Duration`].
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if an error during the parsing process occurred
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    /// use fundu_systemd::TimeSpanParser;
    ///
    /// let parser = TimeSpanParser::new();
    /// assert_eq!(
    ///     parser.parse_with_max("100000000000000000000000000000years", Duration::MAX),
    ///     Ok(Duration::MAX)
    /// );
    /// assert_eq!(
    ///     parser.parse_with_max("123 sec", Duration::positive(1, 0)),
    ///     Ok(Duration::positive(1, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse_with_max("infinity", Duration::positive(i64::MAX as u64, 123)),
    ///     Ok(Duration::positive(i64::MAX as u64, 123))
    /// );
    /// ```
    pub fn parse_with_max(&self, source: &str, max: Duration) -> Result<Duration, ParseError> {
        assert!(max.is_positive());
        let trimmed = trim_whitespace(source);
        match Self::parse_infinity(trimmed, max) {
            Some(duration) => Ok(duration),
            None => self
                .raw
                .parse(trimmed, &TIME_UNITS, None, None)
                .map(|duration| duration.min(max)),
        }
    }

    /// Parse the `source` string into a [`Duration`]
    ///
    /// This method does include the time units for nano seconds unlike the
    /// [`TimeSpanParser::parse`] method. The parser saturates at the maximum [`Duration`] of
    /// `u64::MAX` nano seconds. If you need a different maximum use the
    /// [`TimeSpanParser::parse_nanos_with_max`] method.
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if an error during the parsing process occurred
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    /// use fundu_systemd::{TimeSpanParser, SYSTEMD_MAX_NANOS_DURATION};
    ///
    /// let parser = TimeSpanParser::new();
    /// assert_eq!(
    ///     parser.parse_nanos("2hours"),
    ///     Ok(Duration::positive(2 * 60 * 60, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse_nanos("12.3 seconds"),
    ///     Ok(Duration::positive(12, 300_000_000))
    /// );
    /// assert_eq!(
    ///     parser.parse_nanos("100000000000000000000000000000years"),
    ///     Ok(SYSTEMD_MAX_NANOS_DURATION)
    /// );
    /// assert_eq!(
    ///     parser.parse_nanos("1y 12month"),
    ///     Ok(Duration::positive(63_115_200, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse_nanos("123456789"),
    ///     Ok(Duration::positive(123_456_789, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse_nanos("infinity"),
    ///     Ok(SYSTEMD_MAX_NANOS_DURATION)
    /// );
    /// ```
    pub fn parse_nanos(&self, source: &str) -> Result<Duration, ParseError> {
        self.parse_nanos_with_max(source, SYSTEMD_MAX_NANOS_DURATION)
    }

    /// Parse the `source` string into a [`Duration`] saturating at the given `max` [`Duration`]
    ///
    /// This method does include the time units for nano seconds unlike the
    /// [`TimeSpanParser::parse_with_max`] method
    ///
    /// # Panics
    ///
    /// This method panics if `max` is a a negative [`Duration`].
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if an error during the parsing process occurred
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    /// use fundu_systemd::TimeSpanParser;
    ///
    /// let parser = TimeSpanParser::new();
    /// assert_eq!(
    ///     parser.parse_nanos_with_max("100000000000000000000000000000years", Duration::MAX),
    ///     Ok(Duration::MAX)
    /// );
    /// assert_eq!(
    ///     parser.parse_nanos_with_max("1234567890 nsec", Duration::positive(1, 0)),
    ///     Ok(Duration::positive(1, 0))
    /// );
    /// assert_eq!(
    ///     parser.parse_nanos_with_max("infinity", Duration::positive(i64::MAX as u64, 123)),
    ///     Ok(Duration::positive(i64::MAX as u64, 123))
    /// );
    /// ```
    pub fn parse_nanos_with_max(
        &self,
        source: &str,
        max: Duration,
    ) -> Result<Duration, ParseError> {
        assert!(max.is_positive());
        let trimmed = trim_whitespace(source);
        match Self::parse_infinity(trimmed, max) {
            Some(duration) => Ok(duration),
            None => self
                .raw
                .parse(trimmed, &TIME_UNITS_WITH_NANOS, None, None)
                .map(|duration| duration.min(max)),
        }
    }

    /// Set the default [`TimeUnit`] during runtime
    ///
    /// The default unit is applied to numbers without time units
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{Duration, TimeUnit};
    /// use fundu_systemd::TimeSpanParser;
    ///
    /// let mut parser = TimeSpanParser::with_default_unit(TimeUnit::MicroSecond);
    /// assert_eq!(parser.parse("100"), Ok(Duration::positive(0, 100_000)));
    ///
    /// parser.set_default_unit(TimeUnit::Second);
    /// assert_eq!(parser.parse("100"), Ok(Duration::positive(100, 0)));
    ///
    /// let mut parser = TimeSpanParser::new();
    /// assert_eq!(parser.parse("123456"), Ok(Duration::positive(123456, 0)));
    ///
    /// parser.set_default_unit(TimeUnit::MicroSecond);
    /// assert_eq!(
    ///     parser.parse("123456"),
    ///     Ok(Duration::positive(0, 123_456_000))
    /// );
    /// ```
    pub fn set_default_unit(&mut self, time_unit: TimeUnit) {
        self.raw.config.default_unit = time_unit;
    }
}

impl<'a> Default for TimeSpanParser<'a> {
    fn default() -> Self {
        Self::new()
    }
}

/// This struct is used internally to hold the time units without nano second time units
pub struct TimeUnits {}

impl TimeUnitsLike for TimeUnits {
    #[inline]
    fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        match identifier {
            // These are two different letters: the greek small letter mu U+03BC and the micro sign
            // U+00B5
            "us" | "\u{03bc}s" | "\u{00b5}s" | "usec" => Some(MICRO_SECOND),
            "ms" | "msec" => Some(MILLI_SECOND),
            "s" | "sec" | "second" | "seconds" => Some(SECOND),
            "m" | "min" | "minute" | "minutes" => Some(MINUTE),
            "h" | "hr" | "hour" | "hours" => Some(HOUR),
            "d" | "day" | "days" => Some(DAY),
            "w" | "week" | "weeks" => Some(WEEK),
            "M" | "month" | "months" => Some(MONTH),
            "y" | "year" | "years" => Some(YEAR),
            _ => None,
        }
    }
}

/// This struct is used internally to hold the time units with nano second time units
pub struct TimeUnitsWithNanos {}

impl TimeUnitsLike for TimeUnitsWithNanos {
    #[inline]
    fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        match identifier {
            "ns" | "nsec" => Some(NANO_SECOND),
            // These are two different letters: the greek small letter mu U+03BC and the micro sign
            // U+00B5
            "us" | "\u{03bc}s" | "\u{00b5}s" | "usec" => Some(MICRO_SECOND),
            "ms" | "msec" => Some(MILLI_SECOND),
            "s" | "sec" | "second" | "seconds" => Some(SECOND),
            "m" | "min" | "minute" | "minutes" => Some(MINUTE),
            "h" | "hr" | "hour" | "hours" => Some(HOUR),
            "d" | "day" | "days" => Some(DAY),
            "w" | "week" | "weeks" => Some(WEEK),
            "M" | "month" | "months" => Some(MONTH),
            "y" | "year" | "years" => Some(YEAR),
            _ => None,
        }
    }
}

/// Parse the `source` string into a [`Duration`]
///
/// This method does not include the time units for nano seconds unlike the
/// [`TimeSpanParser::parse_nanos`] method. The parser saturates at the maximum [`Duration`] of
/// `u64::MAX` micro seconds if not specified otherwise. Optionally, it's possible to specify a
/// different default time unit than [`TimeUnit::Second`]
///
/// # Panics
///
/// This method panics if `max` is a a negative [`Duration`].
///
/// # Errors
///
/// Returns a [`ParseError`] if an error during the parsing process occurred
///
/// # Examples
///
/// ```rust
/// use fundu::{Duration, TimeUnit};
/// use fundu_systemd::{parse, SYSTEMD_MAX_MICRO_DURATION};
///
/// assert_eq!(
///     parse("2hours", None, None),
///     Ok(Duration::positive(2 * 60 * 60, 0))
/// );
/// assert_eq!(
///     parse("1y 12month", None, None),
///     Ok(Duration::positive(63_115_200, 0))
/// );
/// assert_eq!(
///     parse("12.3", Some(TimeUnit::MilliSecond), None),
///     Ok(Duration::positive(0, 12_300_000))
/// );
/// assert_eq!(
///     parse("100000000000000000000000000000years", None, None),
///     Ok(SYSTEMD_MAX_MICRO_DURATION)
/// );
/// assert_eq!(
///     parse(
///         "100000000000000000000000000000years",
///         None,
///         Some(Duration::MAX)
///     ),
///     Ok(Duration::MAX)
/// );
/// assert_eq!(
///     parse("infinity", None, None),
///     Ok(SYSTEMD_MAX_MICRO_DURATION)
/// );
/// ```
pub fn parse(
    source: &str,
    default_unit: Option<TimeUnit>,
    max: Option<Duration>,
) -> Result<Duration, ParseError> {
    match default_unit {
        None | Some(TimeUnit::Second) => {
            PARSER.parse_with_max(source, max.unwrap_or(SYSTEMD_MAX_MICRO_DURATION))
        }
        Some(time_unit) => {
            let mut parser = PARSER;
            parser.set_default_unit(time_unit);
            parser.parse_with_max(source, max.unwrap_or(SYSTEMD_MAX_MICRO_DURATION))
        }
    }
}

/// Parse the `source` string into a [`Duration`] with nano second time units
///
/// This method does include the time units for nano seconds unlike the [`parse`] method. The parser
/// saturates at the maximum [`Duration`] of `u64::MAX` nano seconds if not specified otherwise.
/// Optionally, it's possible to specify a different default time unit than [`TimeUnit::Second`]
///
/// # Panics
///
/// This method panics if `max` is a a negative [`Duration`].
///
/// # Errors
///
/// Returns a [`ParseError`] if an error during the parsing process occurred
///
/// # Examples
///
/// ```rust
/// use fundu::{Duration, TimeUnit};
/// use fundu_systemd::{parse_nanos, SYSTEMD_MAX_NANOS_DURATION};
///
/// assert_eq!(
///     parse_nanos("2nsec", None, None),
///     Ok(Duration::positive(0, 2))
/// );
/// assert_eq!(
///     parse_nanos("1y 12month", None, None),
///     Ok(Duration::positive(63_115_200, 0))
/// );
/// assert_eq!(
///     parse_nanos("12.3", Some(TimeUnit::MilliSecond), None),
///     Ok(Duration::positive(0, 12_300_000))
/// );
/// assert_eq!(
///     parse_nanos("100000000000000000000000000000years", None, None),
///     Ok(SYSTEMD_MAX_NANOS_DURATION)
/// );
/// assert_eq!(
///     parse_nanos(
///         "100000000000000000000000000000years",
///         None,
///         Some(Duration::MAX)
///     ),
///     Ok(Duration::MAX)
/// );
/// assert_eq!(
///     parse_nanos("infinity", None, None),
///     Ok(SYSTEMD_MAX_NANOS_DURATION)
/// );
/// ```
pub fn parse_nanos(
    source: &str,
    default_unit: Option<TimeUnit>,
    max: Option<Duration>,
) -> Result<Duration, ParseError> {
    match default_unit {
        None | Some(TimeUnit::Second) => {
            PARSER.parse_nanos_with_max(source, max.unwrap_or(SYSTEMD_MAX_NANOS_DURATION))
        }
        Some(time_unit) => {
            let mut parser = PARSER;
            parser.set_default_unit(time_unit);
            parser.parse_nanos_with_max(source, max.unwrap_or(SYSTEMD_MAX_NANOS_DURATION))
        }
    }
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
mod tests {
    use rstest::rstest;

    use super::*;

    #[test]
    fn test_parser_new() {
        let parser = TimeSpanParser::new();
        assert_eq!(parser.raw.config, CONFIG);
    }

    #[rstest]
    #[case::not_second(TimeUnit::Week)]
    #[case::second(TimeUnit::Second)]
    fn test_parser_with_default_unit(#[case] time_unit: TimeUnit) {
        let parser = TimeSpanParser::with_default_unit(time_unit);
        let mut config = CONFIG;
        config.default_unit = time_unit;
        assert_eq!(parser.raw.config, config);
    }

    #[rstest]
    #[case::not_second(TimeUnit::Week)]
    #[case::second(TimeUnit::Second)]
    fn test_parser_set_default_unit(#[case] time_unit: TimeUnit) {
        let mut config = CONFIG;
        config.default_unit = time_unit;

        let mut parser = TimeSpanParser::new();
        parser.set_default_unit(time_unit);

        assert_eq!(parser.raw.config, config);
    }

    #[test]
    fn test_parser_default() {
        assert_eq!(TimeSpanParser::new(), TimeSpanParser::default());
        assert_eq!(TimeSpanParser::default(), PARSER);
    }

    #[rstest]
    #[case::time_units(&TimeUnits {})]
    #[case::time_units_with_nanos(&TimeUnitsWithNanos {})]
    fn test_time_units_is_not_empty(#[case] time_units_like: &dyn TimeUnitsLike) {
        assert!(!time_units_like.is_empty());
    }
}
