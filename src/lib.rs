// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! # Overview
//!
//! Parse a string in float-like scientific format into a [`std::time::Duration`].
//!
//! `fundu` is a configurable, precise and fast string parser
//!
//! * with customizable [`TimeUnit`]s
//! * without floating point calculations. What you put in is what you get out.
//! * with sound limit handling. Infinity and numbers larger than [`Duration::MAX`] evaluate to
//!   [`Duration::MAX`]. Numbers `x` with `abs(x) < 1e-18` evaluate to [`Duration::ZERO`].
//! * without restrictions on the length of the input string
//! * with helpful error messages
//!
//! # Configuration and Format
//!
//! This parser can be configured to accept strings with a default set of time units
//! [`DurationParser::new`], with all time units [`DurationParser::with_all_time_units`] or
//! without [`DurationParser::without_time_units`]. A custom set of time units is also possible with
//! [`DurationParser::with_time_units`]. All these parsers accept strings such as
//!
//! * `1.41`
//! * `42`
//! * `2e-8`, `2e+8` (or likewise `2.0e8`)
//! * `.5` or likewise `0.5`
//! * `3.` or likewise `3.0`
//! * `inf`, `+inf`, `infinity`, `+infinity`
//!
//! All alphabetic characters are matched case-insensitive, so `InFINity` or `2E8` are absolute
//! valid input strings. Additionally, depending on the chosen set of time units one of the
//! following time units (the first column) are accepted (directly following the number without spaces
//! between them):
//!
//! | [`TimeUnit`]    | default id | is default time unit
//! | --------------- | ----------:|:--------------------:
//! | [`Nanosecond`]  |         ns | yes
//! | [`Microsecond`] |         Ms | yes
//! | [`Millisecond`] |         ms | yes
//! | [`Second`]      |          s | yes
//! | [`Minute`]      |          m | yes
//! | [`Hour`]        |          h | yes
//! | [`Day`]         |          d | yes
//! | [`Week`]        |          w | yes
//! | [`Month`]       |          M |  no
//! | [`Year`]        |          y |  no
//!
//! If no time unit is given and not specified otherwise with [`DurationParser::default_unit`] then
//! `s` (= [`Second`]) is assumed. Some accepted strings with time units
//!
//! * `31.2s`
//! * `200000Ms`
//! * `3.14e8w`
//! * ...
//!
//! # Format specification
//!
//! The time units are case-sensitive, all other alphabetic characters are case-insensitive
//!
//! ```text
//! Duration ::= Sign? ( 'inf' | 'infinity' | ( Number TimeUnit?))
//! TimeUnit ::= ns | Ms | ms | s | m | h | d | w | M | y
//! Number   ::= ( Digit+ |
//!                Digit+ '.' Digit* |
//!                Digit* '.' Digit+ )
//!              Exp?
//! Exp      ::= 'e' Sign? Digit+
//! Sign     ::= [+-]
//! Digit    ::= [0-9]
//! ```
//!
//! Special cases which are not displayed in the specification:
//!
//! * Negative values, including negative infinity are not allowed. For exceptions see the next
//!   point.
//! * Numbers `x` (positive and negative) close to `0` (`abs(x) < 1e-18`) are treated as `0`
//! * Positive infinity and numbers exceeding [`Duration::MAX`] saturate at [`Duration::MAX`]
//! * The exponent must be in the range `-1022 <= Exp <= 1023`
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
//! When a customization of the accepted [`TimeUnit`]s is required, then the builder
//! [`DurationParser`] can be used.
//!
//! ```rust
//! use fundu::{DurationParser};
//! use std::time::Duration;
//!
//! let input = "3m";
//! assert_eq!(DurationParser::with_all_time_units().parse(input).unwrap(), Duration::new(180, 0));
//! ```
//!
//! When no time units are configured, seconds is assumed.
//!
//! ```rust
//! use fundu::{DurationParser};
//! use std::time::Duration;
//!
//! let input = "1.0e2";
//! assert_eq!(DurationParser::without_time_units().parse(input).unwrap(), Duration::new(100, 0));
//! ```
//!
//! However, the following will return an error because `y` (Years) is not a default time unit:
//!
//! ```rust
//! use fundu::{DurationParser};
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
//! Setting the default time unit (if no time unit is given in the input string) to something different
//! than seconds is also easily possible
//!
//! ```rust
//! use fundu::{DurationParser, TimeUnit::*};
//! use std::time::Duration;
//!
//! assert_eq!(
//!     DurationParser::without_time_units().default_unit(MilliSecond).parse("1000").unwrap(),
//!     Duration::new(1, 0)
//! );
//! ```
//!
//! Also, `fundu` tries to give informative error messages
//!
//! ```rust
//! use fundu::{DurationParser};
//! use std::time::Duration;
//!
//! assert_eq!(
//!     DurationParser::without_time_units()
//!         .parse("1y")
//!         .unwrap_err()
//!         .to_string(),
//!     "Time unit error: No time units allowed but found: 'y' at column 1"
//! );
//! ```
//!
//! [`NanoSecond`]: [`TimeUnit::NanoSecond`]
//! [`MicroSecond`]: [`TimeUnit::MicroSecond`]
//! [`MilliSecond`]: [`TimeUnit::MilliSecond`]
//! [`Second`]: [`TimeUnit::Second`]
//! [`Minute`]: [`TimeUnit::Minute`]
//! [`Hour`]: [`TimeUnit::Hour`]
//! [`Day`]: [`TimeUnit::Day`]
//! [`Week`]: [`TimeUnit::Week`]
//! [`Month`]: [`TimeUnit::Month`]
//! [`Year`]: [`TimeUnit::Year`]

mod error;
mod parse;
mod time;

use std::time::Duration;

pub use error::ParseError;
use parse::ReprParser;
pub use time::TimeUnit;
use time::{CustomTimeUnits, IdentifiersSlice, TimeUnits, TimeUnitsLike};
pub use time::{
    DEFAULT_ID_DAY, DEFAULT_ID_HOUR, DEFAULT_ID_MICRO_SECOND, DEFAULT_ID_MILLI_SECOND,
    DEFAULT_ID_MINUTE, DEFAULT_ID_MONTH, DEFAULT_ID_NANO_SECOND, DEFAULT_ID_SECOND,
    DEFAULT_ID_WEEK, DEFAULT_ID_YEAR, SYSTEMD_TIME_UNITS,
};

/// Create a new parser with a custom set of [`TimeUnit`]s.
///
/// See also the [module level documentation](crate) for more details and more information about the
/// format.
///
/// # Examples
///
/// A parser with the default set of time units
///
/// ```rust
/// use fundu::{DurationParser};
/// use std::time::Duration;
///
/// let mut parser = DurationParser::new();
/// assert_eq!(parser.parse("42Ms").unwrap(), Duration::new(0, 42_000));
/// ```
///
/// The parser is reusable and the set of time units is fully customizable
///
///
/// ```rust
/// use fundu::{DurationParser, TimeUnit::*};
/// use std::time::Duration;
//
/// let mut parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);
/// for (input, expected) in &[
///     ("9e3ns", Duration::new(0, 9000)),
///     ("10m", Duration::new(600, 0)),
///     ("1.1h", Duration::new(3960, 0)),
///     ("7", Duration::new(7, 0)),
/// ] {
///     assert_eq!(parser.parse(input).unwrap(), *expected);
/// }
/// ```
pub struct DurationParser {
    time_units: TimeUnits,
    default_unit: TimeUnit,
}

impl DurationParser {
    /// Construct the parser with the default set of [`TimeUnit`]s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(DurationParser::new().parse("1").unwrap(), Duration::new(1, 0));
    /// assert_eq!(DurationParser::new().parse("1s").unwrap(), Duration::new(1, 0));
    /// assert_eq!(DurationParser::new().parse("42.0e9ns").unwrap(), Duration::new(42, 0));
    ///
    /// assert_eq!(
    ///     DurationParser::new().get_current_time_units(),
    ///     vec![NanoSecond, MicroSecond, MilliSecond, Second, Minute, Hour, Day, Week]
    /// );
    /// ```
    pub fn new() -> Self {
        Self {
            time_units: TimeUnits::with_default_time_units(),
            default_unit: Default::default(),
        }
    }

    /// Initialize the parser with a custom set of [`TimeUnit`]s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::with_time_units(&[NanoSecond, Hour, Week]).parse("1.5w").unwrap(),
    ///     Duration::new(60 * 60 * 24 * 7 + 60 * 60 * 24 * 7 / 2, 0)
    /// );
    /// ```
    pub fn with_time_units(time_units: &[TimeUnit]) -> Self {
        Self {
            time_units: TimeUnits::with_time_units(time_units),
            default_unit: Default::default(),
        }
    }

    /// Return a parser without [`TimeUnit`]s.
    ///
    /// Note this is the fastest parser because no time unit setup is required.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units().parse("33.33").unwrap(),
    ///     Duration::new(33, 330_000_000)
    /// );
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units().get_current_time_units(),
    ///     vec![]
    /// );
    /// ```
    pub fn without_time_units() -> Self {
        Self {
            time_units: TimeUnits::new(),
            default_unit: Default::default(),
        }
    }

    /// Construct a parser with all available [`TimeUnit`]s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::with_all_time_units().get_current_time_units(),
    ///     vec![NanoSecond, MicroSecond, MilliSecond, Second, Minute, Hour, Day, Week, Month, Year]
    /// );
    /// ```
    pub fn with_all_time_units() -> Self {
        Self {
            time_units: TimeUnits::with_all_time_units(),
            default_unit: Default::default(),
        }
    }

    /// Set the default [`TimeUnit`] to `unit`.
    ///
    /// The default time unit is applied when no time unit was given in the input string. If the
    /// default time unit is not set with this method the parser defaults to [`TimeUnit::Second`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::with_all_time_units().default_unit(NanoSecond).parse("42").unwrap(),
    ///     Duration::new(0, 42)
    /// );
    /// ```
    pub fn default_unit(&mut self, unit: TimeUnit) -> &mut Self {
        self.default_unit = unit;
        self
    }

    pub fn get_current_time_units(&self) -> Vec<TimeUnit> {
        self.time_units.get_time_units()
    }

    /// Add a time unit to the current set of [`TimeUnit`]s.
    ///
    /// Adding an already existing [`TimeUnit`] has no effect.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::new().time_unit(Month).time_unit(Year).get_current_time_units(),
    ///     DurationParser::with_all_time_units().get_current_time_units(),
    /// );
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units().time_unit(Second).get_current_time_units(),
    ///     vec![Second],
    /// );
    /// ```
    pub fn time_unit(&mut self, unit: TimeUnit) -> &mut Self {
        self.time_units.add_time_unit(unit);
        self
    }

    /// Add multiple [`TimeUnit`]s to the current set of time units.
    ///
    /// Adding a [`TimeUnit`] which is already present has no effect.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units().time_units(&[MicroSecond, MilliSecond]).get_current_time_units(),
    ///     vec![MicroSecond, MilliSecond],
    /// );
    /// ```
    pub fn time_units(&mut self, units: &[TimeUnit]) -> &mut Self {
        self.time_units.add_time_units(units);
        self
    }

    /// Parse the `source` string into a [`std::time::Duration`] depending on the current set of
    /// configured [`TimeUnit`]s.
    ///
    /// See the [module level documentation](crate) for more information on the format.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse("1.2e-1s").unwrap(),
    ///     Duration::new(0, 120_000_000),
    /// );
    /// ```
    #[inline(never)]
    pub fn parse(&mut self, source: &str) -> Result<Duration, ParseError> {
        let mut parser = ReprParser::new(source, self.default_unit, &self.time_units);
        parser.parse().and_then(|mut repr| repr.parse())
    }
}

impl Default for DurationParser {
    fn default() -> Self {
        Self::new()
    }
}

pub struct CustomDurationParser<'a> {
    time_units: CustomTimeUnits<'a>,
    default_unit: TimeUnit,
}

impl<'a> CustomDurationParser<'a> {
    pub fn new() -> Self {
        Self {
            time_units: CustomTimeUnits::new(),
            default_unit: Default::default(),
        }
    }

    pub fn with_default_time_units() -> Self {
        Self {
            time_units: CustomTimeUnits::with_default_time_units(),
            default_unit: Default::default(),
        }
    }

    pub fn with_time_units(units: &'a [IdentifiersSlice<'a>]) -> Self {
        Self {
            time_units: CustomTimeUnits::with_time_units(units),
            default_unit: Default::default(),
        }
    }

    /// Set the default [`TimeUnit`] to `unit`.
    ///
    /// The default time unit is applied when no time unit was given in the input string. If the
    /// default time unit is not set with this method the parser defaults to [`TimeUnit::Second`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::with_all_time_units().default_unit(NanoSecond).parse("42").unwrap(),
    ///     Duration::new(0, 42)
    /// );
    /// ```
    pub fn default_unit(&mut self, unit: TimeUnit) -> &mut Self {
        self.default_unit = unit;
        self
    }

    pub fn get_current_time_units(&self) -> Vec<TimeUnit> {
        self.time_units.get_time_units()
    }

    /// Add a time unit to the current set of [`TimeUnit`]s.
    ///
    /// Adding an already existing [`TimeUnit`] has no effect.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::new().time_unit(Month).time_unit(Year).get_current_time_units(),
    ///     DurationParser::with_all_time_units().get_current_time_units(),
    /// );
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units().time_unit(Second).get_current_time_units(),
    ///     vec![Second],
    /// );
    /// ```
    pub fn time_unit(&mut self, unit: IdentifiersSlice<'a>) -> &mut Self {
        self.time_units.add_time_unit(unit);
        self
    }

    /// Add multiple [`TimeUnit`]s to the current set of time units.
    ///
    /// Adding a [`TimeUnit`] which is already present has no effect.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units().time_units(&[MicroSecond, MilliSecond]).get_current_time_units(),
    ///     vec![MicroSecond, MilliSecond],
    /// );
    /// ```
    pub fn time_units(&mut self, units: &'a [IdentifiersSlice]) -> &mut Self {
        self.time_units.add_time_units(units);
        self
    }

    /// Parse the `source` string into a [`std::time::Duration`] depending on the current set of
    /// configured [`TimeUnit`]s.
    ///
    /// See the [module level documentation](crate) for more information on the format.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse("1.2e-1s").unwrap(),
    ///     Duration::new(0, 120_000_000),
    /// );
    /// ```
    #[inline(never)]
    pub fn parse(&mut self, source: &str) -> Result<Duration, ParseError> {
        let mut parser = ReprParser::new(source, self.default_unit, &self.time_units);
        parser.parse().and_then(|mut repr| repr.parse())
    }
}

impl<'a> Default for CustomDurationParser<'a> {
    fn default() -> Self {
        Self::new()
    }
}

/// Parse a string into a [`std::time::Duration`] by accepting a `string` similar to floating point
/// with the default set of time units.
///
/// This method is basically the same like [`DurationParser::new`] providing a simple to setup
/// onetime parser. It is generally a better idea to use the [`DurationParser`] builder if multiple
/// inputs with the same set of time unit need to be parsed.
///
/// See also the [module level documentation](crate) for more details and more information about the format.
///
/// # Errors
///
/// This function returns a [`ParseError`] when parsing of the input `string` failed.
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
/// assert_eq!(
///     parse_duration("Not a number"),
///     Err(ParseError::Syntax(0, "Invalid character: 'N'".to_string()))
/// );
/// ```
pub fn parse_duration(string: &str) -> Result<Duration, ParseError> {
    DurationParser::new().parse(string)
}
