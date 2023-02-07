// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! # Overview
//!
//! `fundu` provides a duration parser to parse strings into a [`std::time::Duration`]. It tries
//! to improve on the standard method `Duration::from_secs_f64(input.parse().unwrap())` by
//!
//! * Providing customizable [`TimeUnit`]s which are accepted in the input string. See table below.
//! * Using no floating point calculations and precisely parse the input as it is. So, what you put
//! in you is what you get out within the range of a [`std::time::Duration`].
//! * Evaluating to [`std::time::Duration::MAX`] if the input number was larger than that maximum or
//! the input string was positive `infinity`
//! * Providing better error messages in case of parsing errors.
//!
//! These features come with almost no additional runtime costs by still being a lightweight crate.
//! This crate is built on top of the rust `stdlib`, so no additional dependencies are required. The
//! accepted number format is very close to the scientific floating point format. See the format
//! specification below for details.
//!
//! # Examples
//!
//! If only the default configuration is required, the [`parse_duration`] method can be used.
//!
//! ```rust
//! use fundu::parse_duration;
//! use std::time::Duration;
//!
//! let input = "1.0e2s";
//! assert_eq!(parse_duration(input).unwrap(), Duration::new(100, 0));
//! ```
//!
//! When a customization of the accepted [`TimeUnit`] is required, then the builder
//! [`DurationParser`] can be used.
//!
//! ```rust
//! use fundu::DurationParser;
//! use std::time::Duration;
//!
//! let input = "3m";
//! assert_eq!(DurationParser::with_all_time_units().parse(input).unwrap(), Duration::new(180, 0));
//! ```
//!
//! When no time units are configured, seconds is assumed.
//!
//! ```rust
//! use fundu::DurationParser;
//! use std::time::Duration;
//!
//! let input = "1.0e2";
//! assert_eq!(DurationParser::without_time_units().parse(input).unwrap(), Duration::new(100, 0));
//! ```
//!
//! However, this will return an error because `y` (Years) is not a default time unit.
//!
//! ```rust
//! use fundu::DurationParser;
//!
//! let input = "3y";
//! assert!(DurationParser::new().parse(input).is_err());
//! ```
//!
//! The parser is reusable and the set of time units is fully customizable
//!
//! ```rust
//! use fundu::{DurationParser, TimeUnit::*};
//! use std::time::Duration;
//!
//! let mut parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);
//! for (input, expected) in &[
//!     ("9e3ns", Duration::new(0, 9000)),
//!     ("10m", Duration::new(600, 0)),
//!     ("1.1h", Duration::new(3960, 0)),
//!     ("7", Duration::new(7, 0)),
//! ] {
//!     assert_eq!(parser.parse(input).unwrap(), *expected);
//! }
//! ```
//!
//! Also, `fundu` tries to give informative error messages
//!
//! ```rust
//! use fundu::DurationParser;
//! use std::time::Duration;
//!
//! assert_eq!(
//!     DurationParser::without_time_units()
//!         .parse("1y")
//!         .unwrap_err()
//!         .to_string(),
//!     "Syntax error: No time units allowed but found: 'y' at column 1"
//! );
//! ```
//!
//! # Format specification
//!
//! ```text
//! Duration ::= Sign?                                       # No negative values besides negative zero
//!              ( 'inf' | 'infinity' | Number )             # 'inf' and 'infinity' are case insensitive
//! TimeUnit ::= ns | Ms | ms | s | m | h | d | w | M | y    # The accepted units are customizable
//! Number   ::= ( Digit+ |
//!                Digit+ '.' Digit* |
//!                Digit* '.' Digit+ )
//!               Exp?                                       # -1022 <= EXP <= 1023
//!               TimeUnit?                                  # If no time unit then seconds is assumed
//! Exp      ::= [eE] Sign? Digit+
//! Sign     ::= [+-]
//! Digit    ::= [0-9]
//! ```

mod error;
mod parse;
mod time;

pub use error::ParseError;
use parse::ReprParser;
use std::time::Duration;
pub use time::TimeUnit;
use time::TimeUnits;
pub use time::{
    DEFAULT_ID_DAY, DEFAULT_ID_HOUR, DEFAULT_ID_MICRO_SECOND, DEFAULT_ID_MILLI_SECOND,
    DEFAULT_ID_MINUTE, DEFAULT_ID_MONTH, DEFAULT_ID_NANO_SECOND, DEFAULT_ID_SECOND,
    DEFAULT_ID_WEEK, DEFAULT_ID_YEAR,
};

/// A builder with methods to configure the parser with a set of time units.
#[derive(Debug, Default)]
pub struct DurationParser {
    time_units: TimeUnits,
}

impl DurationParser {
    /// Construct the parser with default time units.
    pub fn new() -> Self {
        Self {
            time_units: TimeUnits::with_default_time_units(),
        }
    }

    /// Initialize the parser with a custom set of time units.
    pub fn with_time_units(time_units: &[TimeUnit]) -> Self {
        Self {
            time_units: TimeUnits::with_time_units(time_units),
        }
    }

    /// Return a parser without time units.
    ///
    /// This is the fastest parser.
    pub fn without_time_units() -> Self {
        Self {
            time_units: TimeUnits::new(),
        }
    }

    /// Construct a parser with all available time units.
    pub fn with_all_time_units() -> Self {
        Self {
            time_units: TimeUnits::with_all_time_units(),
        }
    }

    /// Add a time unit to the current set of time units.
    pub fn time_unit(&mut self, unit: TimeUnit) -> &mut Self {
        self.time_units.add_time_unit(unit);
        self
    }

    /// Add a list of time unit to the current set of time units.
    pub fn time_units(&mut self, units: &[TimeUnit]) -> &mut Self {
        self.time_units.add_time_units(units);
        self
    }

    /// Parse the `source` string into a duration.
    pub fn parse(&mut self, source: &str) -> Result<Duration, ParseError> {
        let mut parser = ReprParser::new(source, &self.time_units);
        parser.parse().and_then(|mut repr| repr.parse())
    }

    /// Return all [`TimeUnit`]s in the current set of time units.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::with_all_time_units().get_time_units(),
    ///     vec![NanoSecond, MicroSecond, MilliSecond, Second, Minute, Hour, Day, Week, Month, Year]
    /// );
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units().time_units(&[MicroSecond, MilliSecond]).get_time_units(),
    ///     vec![MicroSecond, MilliSecond],
    /// );
    /// ```
    pub fn get_time_units(&self) -> Vec<TimeUnit> {
        self.time_units.get_time_units()
    }
}

/// Parse a string into a [`Duration`] by accepting a source string similar to floating point with
/// the default set of time units.
///
/// No whitespace is allowed in the source string. By parsing directly into a `u64` for the whole
/// number part (the [`Duration`] seconds) and `u32` for the fraction part (the [`Duration`] nano
/// seconds), we avoid the possibly lossy intermediate conversion to a `f64` and can represent the
/// exact user input as `Duration`. We can also represent valid durations, which
/// [`Duration::from_secs_f64`] can not parse without errors, like `format!("{}.0", u64::MAX)`. The
/// accepted grammar is (closely related to [`f64::from_str`]):
///
/// The parsed [`Duration`] saturates at `seconds == u64::MAX`, `nanos (max) == .999999999` and is
/// bounded below at `nanos (min if not 0) == .000000001`. Infinity values like `inf`, `+infinity`
/// etc. are valid input and resolve to `Duration::MAX`.
///
/// # Errors
///
/// This function will return an error when parsing fails, the `src` was negative (`-0.0` counts as
/// not negative) or the exponent wasn't in the allowed range (`-1022..=1023`).
///
/// # Examples
///
/// ```rust
/// use fundu::{parse_duration, ParseError};
/// use std::time::Duration;
///
/// let duration = parse_duration("+1.09e1").unwrap();
/// assert_eq!(duration, Duration::new(10, 900_000_000));
///
/// assert_eq!(parse_duration("Not a number"), Err(ParseError::Syntax(0, "Invalid character: 'N'".to_string())));
/// ```
///
/// [`f64::from_str`]: https://doc.rust-lang.org/std/primitive.f64.html#method.from_str
pub fn parse_duration(string: &str) -> Result<Duration, ParseError> {
    DurationParser::new().parse(string)
}
