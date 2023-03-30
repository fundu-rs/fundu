// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use super::config::{Config, Delimiter};
use crate::parse::Parser;
use crate::time::{Multiplier, TimeUnitsLike};
use crate::TimeUnit::*;
use crate::{
    ParseError, TimeUnit, DEFAULT_ID_DAY, DEFAULT_ID_HOUR, DEFAULT_ID_MICRO_SECOND,
    DEFAULT_ID_MILLI_SECOND, DEFAULT_ID_MINUTE, DEFAULT_ID_MONTH, DEFAULT_ID_NANO_SECOND,
    DEFAULT_ID_SECOND, DEFAULT_ID_WEEK, DEFAULT_ID_YEAR,
};

const DEFAULT_TIME_UNITS: [&str; 10] = [
    DEFAULT_ID_NANO_SECOND,
    DEFAULT_ID_MICRO_SECOND,
    DEFAULT_ID_MILLI_SECOND,
    DEFAULT_ID_SECOND,
    DEFAULT_ID_MINUTE,
    DEFAULT_ID_HOUR,
    DEFAULT_ID_DAY,
    DEFAULT_ID_WEEK,
    DEFAULT_ID_MONTH,
    DEFAULT_ID_YEAR,
];

/// Interface for [`TimeUnit`]s providing common methods to manipulate the available time units.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TimeUnits {
    data: [Option<TimeUnit>; 10],
}

impl Default for TimeUnits {
    fn default() -> Self {
        Self::with_default_time_units()
    }
}

impl TimeUnitsLike for TimeUnits {
    /// Return `true` if this set of time units is empty.
    fn is_empty(&self) -> bool {
        self.data.iter().all(|byte| byte.is_none())
    }

    /// Return the [`TimeUnit`] associated with the provided `identifier`.
    ///
    /// Returns `None` if no [`TimeUnit`] with the provided `identifier` is present in the current
    /// set of time units.
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        match identifier.len() {
            1 => self.data.iter().skip(3).filter_map(|t| *t).find_map(|t| {
                let unit = DEFAULT_TIME_UNITS[t as usize];
                if unit == identifier {
                    Some((t, Multiplier::default()))
                } else {
                    None
                }
            }),
            2 => self.data.iter().take(3).filter_map(|t| *t).find_map(|t| {
                let unit = DEFAULT_TIME_UNITS[t as usize];
                if unit == identifier {
                    Some((t, Multiplier::default()))
                } else {
                    None
                }
            }),
            _ => None,
        }
    }
}

impl TimeUnits {
    /// Create an empty set of [`TimeUnit`]s.
    const fn new() -> Self {
        Self { data: [None; 10] }
    }

    /// Create [`TimeUnits`] with a custom set of [`TimeUnit`]s.
    fn with_time_units(units: &[TimeUnit]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

    /// Create [`TimeUnits`] with default [`TimeUnit`]s.
    const fn with_default_time_units() -> Self {
        Self {
            data: [
                Some(NanoSecond),
                Some(MicroSecond),
                Some(MilliSecond),
                Some(Second),
                Some(Minute),
                Some(Hour),
                Some(Day),
                Some(Week),
                None,
                None,
            ],
        }
    }

    /// Create [`TimeUnits`] with a all available [`TimeUnit`]s.
    const fn with_all_time_units() -> Self {
        Self {
            data: [
                Some(NanoSecond),
                Some(MicroSecond),
                Some(MilliSecond),
                Some(Second),
                Some(Minute),
                Some(Hour),
                Some(Day),
                Some(Week),
                Some(Month),
                Some(Year),
            ],
        }
    }

    /// Add a [`TimeUnit`] to the set of already present time units.
    fn add_time_unit(&mut self, unit: TimeUnit) {
        self.data[unit as usize] = Some(unit);
    }

    /// Add multiple [`TimeUnit`] to the set of already present time units.
    fn add_time_units(&mut self, units: &[TimeUnit]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    /// Return all [`TimeUnit`]s from the set of active time units ordered.
    fn get_time_units(&self) -> Vec<TimeUnit> {
        self.data.iter().filter_map(|&p| p).collect()
    }
}

/// A parser with a customizable set of [`TimeUnit`]s with default identifiers.
///
/// See also the [module level documentation](crate) for more details and more information about
/// the format.
///
/// # Examples
///
/// A parser with the default set of time units
///
/// ```rust
/// use std::time::Duration;
///
/// use fundu::DurationParser;
///
/// let parser = DurationParser::new();
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
/// let parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);
/// for (input, expected) in &[
///     ("9e3ns", Duration::new(0, 9000)),
///     ("10m", Duration::new(600, 0)),
///     ("1.1h", Duration::new(3960, 0)),
///     ("7", Duration::new(7, 0)),
/// ] {
///     assert_eq!(parser.parse(input).unwrap(), *expected);
/// }
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct DurationParser {
    time_units: TimeUnits,
    inner: Parser,
}

impl DurationParser {
    /// Construct the parser with the default set of [`TimeUnit`]s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse("1").unwrap(),
    ///     Duration::new(1, 0)
    /// );
    /// assert_eq!(
    ///     DurationParser::new().parse("1s").unwrap(),
    ///     Duration::new(1, 0)
    /// );
    /// assert_eq!(
    ///     DurationParser::new().parse("42.0e9ns").unwrap(),
    ///     Duration::new(42, 0)
    /// );
    ///
    /// assert_eq!(
    ///     DurationParser::new().get_current_time_units(),
    ///     vec![
    ///         NanoSecond,
    ///         MicroSecond,
    ///         MilliSecond,
    ///         Second,
    ///         Minute,
    ///         Hour,
    ///         Day,
    ///         Week
    ///     ]
    /// );
    /// ```
    pub const fn new() -> Self {
        Self {
            time_units: TimeUnits::with_default_time_units(),
            inner: Parser::new(),
        }
    }

    /// Initialize the parser with a custom set of [`TimeUnit`]s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParser::with_time_units(&[NanoSecond, Hour, Week])
    ///         .parse("1.5w")
    ///         .unwrap(),
    ///     Duration::new(60 * 60 * 24 * 7 + 60 * 60 * 24 * 7 / 2, 0)
    /// );
    /// ```
    pub fn with_time_units(time_units: &[TimeUnit]) -> Self {
        Self {
            time_units: TimeUnits::with_time_units(time_units),
            inner: Parser::new(),
        }
    }

    /// Return a parser without [`TimeUnit`]s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
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
    pub const fn without_time_units() -> Self {
        Self {
            time_units: TimeUnits::new(),
            inner: Parser::new(),
        }
    }

    /// Construct a parser with all available [`TimeUnit`]s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::DurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParser::with_all_time_units().get_current_time_units(),
    ///     vec![
    ///         NanoSecond,
    ///         MicroSecond,
    ///         MilliSecond,
    ///         Second,
    ///         Minute,
    ///         Hour,
    ///         Day,
    ///         Week,
    ///         Month,
    ///         Year
    ///     ]
    /// );
    /// ```
    pub const fn with_all_time_units() -> Self {
        Self {
            time_units: TimeUnits::with_all_time_units(),
            inner: Parser::new(),
        }
    }

    /// Use the [`DurationParserBuilder`] to construct a [`DurationParser`].
    ///
    /// The [`DurationParserBuilder`] is more ergonomic in some use cases than using
    /// [`DurationParser`] directly. Using this method is the same like invoking
    /// [`DurationParserBuilder::default`].
    ///
    /// See [`DurationParserBuilder`] for more details.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// let parser = DurationParser::builder()
    ///     .all_time_units()
    ///     .default_unit(MicroSecond)
    ///     .allow_delimiter(|byte| byte.is_ascii_whitespace())
    ///     .build();
    ///
    /// assert_eq!(parser.parse("1 \t\nns").unwrap(), Duration::new(0, 1));
    /// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
    ///
    /// // instead of
    ///
    /// let mut parser = DurationParser::with_all_time_units();
    /// parser
    ///     .default_unit(MicroSecond)
    ///     .allow_delimiter(Some(|byte| byte == b' '));
    ///
    /// assert_eq!(parser.parse("1 ns").unwrap(), Duration::new(0, 1));
    /// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
    /// ```
    pub const fn builder<'a>() -> DurationParserBuilder<'a> {
        DurationParserBuilder::new()
    }

    /// Parse the `source` string into a [`std::time::Duration`] depending on the current set of
    /// configured [`TimeUnit`]s.
    ///
    /// See the [module-level documentation](crate) for more information on the format.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse("1.2e-1s").unwrap(),
    ///     Duration::new(0, 120_000_000),
    /// );
    /// ```
    #[inline]
    pub fn parse(&self, source: &str) -> Result<Duration, ParseError> {
        self.inner.parse(source, &self.time_units)
    }

    /// Parse a source string into a [`time::Duration`] which can be negative.
    ///
    /// This method is only available when activating the `negative` feature and saturates at
    /// [`time::Duration::MIN`] for parsed negative durations and at [`time::Duration::MAX`] for
    /// positive durations.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::DurationParser;
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse_negative("-10.2e-1s").unwrap(),
    ///     time::Duration::new(-1, -20_000_000),
    /// );
    /// assert_eq!(
    ///     DurationParser::new().parse_negative("1.2e-1s").unwrap(),
    ///     time::Duration::new(0, 120_000_000),
    /// );
    /// ```
    #[cfg(feature = "negative")]
    #[inline]
    pub fn parse_negative(&self, source: &str) -> Result<time::Duration, ParseError> {
        self.inner.parse_negative(source, &self.time_units)
    }

    /// Set the default [`TimeUnit`] to `unit`.
    ///
    /// The default time unit is applied when no time unit was given in the input string. If the
    /// default time unit is not set with this method the parser defaults to [`TimeUnit::Second`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParser::with_all_time_units()
    ///         .default_unit(NanoSecond)
    ///         .parse("42")
    ///         .unwrap(),
    ///     Duration::new(0, 42)
    /// );
    /// ```
    pub fn default_unit(&mut self, unit: TimeUnit) -> &mut Self {
        self.inner.config.default_unit = unit;
        self
    }

    /// If `Some`, allow one or more [`Delimiter`] between the number and the [`TimeUnit`].
    ///
    /// A [`Delimiter`] is defined as closure taking a byte and returning true if the delimiter
    /// matched. Per default no delimiter is allowed between the number and the [`TimeUnit`]. Note
    /// this setting implicitly allows the delimiter at the end of the string, but only if no time
    /// unit was present. As usual the default time unit is assumed.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::{DurationParser, ParseError};
    ///
    /// let mut parser = DurationParser::new();
    /// assert_eq!(
    ///     parser.parse("123 ns"),
    ///     Err(ParseError::TimeUnit(
    ///         3,
    ///         "Invalid time unit: ' ns'".to_string()
    ///     ))
    /// );
    ///
    /// parser.allow_delimiter(Some(|byte| byte == b' '));
    /// assert_eq!(parser.parse("123 ns"), Ok(Duration::new(0, 123)));
    ///
    /// parser.allow_delimiter(Some(|byte| matches!(byte, b'\t' | b'\n' | b'\r' | b' ')));
    /// assert_eq!(parser.parse("123 ns"), Ok(Duration::new(0, 123)));
    /// assert_eq!(parser.parse("123\t\n\r ns"), Ok(Duration::new(0, 123)));
    /// ```
    pub fn allow_delimiter(&mut self, delimiter: Option<Delimiter>) -> &mut Self {
        self.inner.config.allow_delimiter = delimiter;
        self
    }

    /// If true, disable parsing an exponent.
    ///
    /// If an exponent is encountered in the input string and this setting is active this results
    /// in an [`ParseError::Syntax`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, ParseError};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.disable_exponent(true);
    /// assert_eq!(
    ///     parser.parse("123e+1"),
    ///     Err(ParseError::Syntax(3, "No exponent allowed".to_string()))
    /// );
    /// ```
    pub fn disable_exponent(&mut self, value: bool) -> &mut Self {
        self.inner.config.disable_exponent = value;
        self
    }

    /// If true, disable parsing a fraction in the source string.
    ///
    /// This setting will disable parsing a fraction and a point delimiter will cause an error
    /// [`ParseError::Syntax`]. It does not prevent [`Duration`]s from being smaller than seconds.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::{DurationParser, ParseError};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.disable_fraction(true);
    ///
    /// assert_eq!(
    ///     parser.parse("123.456"),
    ///     Err(ParseError::Syntax(3, "No fraction allowed".to_string()))
    /// );
    ///
    /// assert_eq!(parser.parse("123e-2"), Ok(Duration::new(1, 230_000_000)));
    ///
    /// assert_eq!(parser.parse("123ns"), Ok(Duration::new(0, 123)));
    /// ```
    pub fn disable_fraction(&mut self, value: bool) -> &mut Self {
        self.inner.config.disable_fraction = value;
        self
    }

    /// If true, disable parsing infinity
    ///
    /// This setting will disable parsing infinity values like (`inf` or `infinity`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, ParseError};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.disable_infinity(true);
    ///
    /// assert_eq!(
    ///     parser.parse("inf"),
    ///     Err(ParseError::Syntax(0, format!("Invalid input: 'inf'")))
    /// );
    /// assert_eq!(
    ///     parser.parse("infinity"),
    ///     Err(ParseError::Syntax(0, format!("Invalid input: 'infinity'")))
    /// );
    /// assert_eq!(
    ///     parser.parse("+inf"),
    ///     Err(ParseError::Syntax(1, format!("Invalid input: 'inf'")))
    /// );
    /// ```
    pub fn disable_infinity(&mut self, value: bool) -> &mut Self {
        self.inner.config.disable_infinity = value;
        self
    }

    /// If true, this setting makes a number in the source string optional.
    ///
    /// If no number is present, then `1` is assumed. If a number is present then it must still
    /// consist of either a whole part or fraction part, if not disabled with
    /// [`DurationParser::disable_fraction`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    ///
    /// let mut parser = DurationParser::new();
    /// parser.number_is_optional(true);
    ///
    /// for input in &["ns", "e-9", "e-3Ms"] {
    ///     assert_eq!(parser.parse(input), Ok(Duration::new(0, 1)));
    /// }
    /// ```
    pub fn number_is_optional(&mut self, value: bool) -> &mut Self {
        self.inner.config.number_is_optional = value;
        self
    }

    /// If set to some [`Delimiter`], parse possibly multiple durations and sum them up.
    ///
    /// If [`Delimiter`] is set to `None`, this functionality is disabled. The [`Delimiter`] may or
    /// may not occur to separate the durations. If the delimiter does not occur the next duration
    /// is recognized by a leading digit.
    ///
    /// Like a single duration, the summed up durations saturate at [`Duration::MAX`]. Parsing
    /// multiple durations is short-circuiting and parsing stops after the first [`ParseError`]
    /// was encountered. Note that parsing doesn't stop when reaching [`Duration::MAX`], so any
    /// [`ParseError`]s later in the input string are still reported.
    ///
    /// # Usage together with number format customizations
    ///
    /// The number format and other aspects can be customized as usual via the methods within this
    /// struct and have the known effect. However, there are some interesting constellations:
    ///
    /// If [`DurationParser::allow_delimiter`] is set to some delimiter, the [`Delimiter`] of this
    /// method and the [`Delimiter`] of the `allow_delimiter` method can be equal either in parts or
    /// in a whole without having side-effects on each other. But, if simultaneously
    /// [`DurationParser::number_is_optional`] is set to true, then the resulting [`Duration`] will
    /// differ:
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    ///
    /// let delimiter = |byte| matches!(byte, b' ' | b'\t');
    /// let mut parser = DurationParser::new();
    /// parser
    ///     .parse_multiple(Some(delimiter))
    ///     .number_is_optional(true);
    ///
    /// // Here, the parser parses `1`, `s`, `1` and then `ns` separately
    /// assert_eq!(parser.parse("1 s 1 ns"), Ok(Duration::new(3, 1)));
    ///
    /// // Here, the parser parses `1 s` and then `1 ns`.
    /// parser.allow_delimiter(Some(delimiter));
    /// assert_eq!(parser.parse("1 s 1 ns"), Ok(Duration::new(1, 1)));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    ///
    /// let mut parser = DurationParser::new();
    /// parser.parse_multiple(Some(|byte| matches!(byte, b' ' | b'\t')));
    ///
    /// assert_eq!(parser.parse("1.5h 2e+2ns"), Ok(Duration::new(5400, 200)));
    /// assert_eq!(parser.parse("55s500ms"), Ok(Duration::new(55, 500_000_000)));
    /// assert_eq!(parser.parse("1\t1"), Ok(Duration::new(2, 0)));
    /// assert_eq!(parser.parse("1.   .1"), Ok(Duration::new(1, 100_000_000)));
    /// assert_eq!(parser.parse("2h"), Ok(Duration::new(2 * 60 * 60, 0)));
    /// assert_eq!(
    ///     parser.parse("300ms20s 5d"),
    ///     Ok(Duration::new(5 * 60 * 60 * 24 + 20, 300_000_000))
    /// );
    /// ```
    pub fn parse_multiple(&mut self, delimiter: Option<Delimiter>) -> &mut Self {
        self.inner.config.multiple = delimiter;
        self
    }

    /// Return the currently defined set of [`TimeUnit`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    ///
    /// let parser = DurationParser::without_time_units();
    /// assert_eq!(
    ///     parser.get_current_time_units(),
    ///     vec![]
    /// );
    ///
    /// assert_eq!(
    ///     DurationParser::with_time_units(&[NanoSecond]).get_current_time_units(),
    ///     vec![NanoSecond]
    /// );
    // TODO: rename to current_time_units
    pub fn get_current_time_units(&self) -> Vec<TimeUnit> {
        self.time_units.get_time_units()
    }
}

impl Default for DurationParser {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, PartialEq, Eq)]
enum TimeUnitsChoice<'a> {
    Default,
    All,
    None,
    Custom(&'a [TimeUnit]),
}

/// An ergonomic builder for a [`DurationParser`].
///
/// The [`DurationParserBuilder`] is more ergonomic in some use cases than using
/// [`DurationParser`] directly, especially when using the `DurationParser` for parsing multiple
/// inputs.
///
/// # Examples
///
/// ```rust
/// use std::time::Duration;
///
/// use fundu::TimeUnit::*;
/// use fundu::{DurationParser, DurationParserBuilder};
///
/// let parser = DurationParserBuilder::new()
///     .all_time_units()
///     .default_unit(MicroSecond)
///     .allow_delimiter(|byte| byte == b' ')
///     .build();
///
/// assert_eq!(parser.parse("1   ns").unwrap(), Duration::new(0, 1));
/// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
///
/// // instead of
///
/// let mut parser = DurationParser::with_all_time_units();
/// parser
///     .default_unit(MicroSecond)
///     .allow_delimiter(Some(|byte| byte == b' '));
///
/// assert_eq!(parser.parse("1    ns").unwrap(), Duration::new(0, 1));
/// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct DurationParserBuilder<'a> {
    time_units_choice: TimeUnitsChoice<'a>,
    config: Config,
}

impl<'a> Default for DurationParserBuilder<'a> {
    /// Construct a new [`DurationParserBuilder`] without any time units.
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> DurationParserBuilder<'a> {
    /// Construct a new reusable [`DurationParserBuilder`].
    ///
    /// This method is the same like invoking [`DurationParserBuilder::default`]. Per default
    /// there are no time units configured in the builder. Use one of
    ///
    /// * [`DurationParserBuilder::default_time_units`]
    /// * [`DurationParserBuilder::all_time_units`]
    /// * [`DurationParserBuilder::custom_time_units`]
    ///
    /// to add time units.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, DurationParserBuilder};
    ///
    /// assert_eq!(
    ///     DurationParserBuilder::new().build(),
    ///     DurationParser::without_time_units()
    /// );
    /// ```
    pub const fn new() -> Self {
        Self {
            time_units_choice: TimeUnitsChoice::None,
            config: Config::new(),
        }
    }

    /// Configure [`DurationParserBuilder`] to build the [`DurationParser`] with default time
    /// units.
    ///
    /// Setting the time units with this method overwrites any previously made choices with
    ///
    /// * [`DurationParserBuilder::all_time_units`]
    /// * [`DurationParserBuilder::custom_time_units`]
    ///
    /// The default time units with their identifiers are:
    ///
    /// | [`TimeUnit`]    | default id
    /// | --------------- | ----------:
    /// | Nanosecond  |         ns
    /// | Microsecond |         Ms
    /// | Millisecond |         ms
    /// | Second      |          s
    /// | Minute      |          m
    /// | Hour        |          h
    /// | Day         |          d
    /// | Week        |          w
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::DurationParserBuilder;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParserBuilder::new()
    ///         .default_time_units()
    ///         .build()
    ///         .get_current_time_units(),
    ///     vec![
    ///         NanoSecond,
    ///         MicroSecond,
    ///         MilliSecond,
    ///         Second,
    ///         Minute,
    ///         Hour,
    ///         Day,
    ///         Week
    ///     ]
    /// );
    /// ```
    pub fn default_time_units(&mut self) -> &mut Self {
        self.time_units_choice = TimeUnitsChoice::Default;
        self
    }

    /// Configure [`DurationParserBuilder`] to build the [`DurationParser`] with all time units.
    ///
    /// Setting the time units with this method overwrites any previously made choices with
    ///
    /// * [`DurationParserBuilder::default_time_units`]
    /// * [`DurationParserBuilder::custom_time_units`]
    ///
    /// The time units with their identifiers are:
    ///
    /// | [`TimeUnit`]    | default id
    /// | --------------- | ----------:
    /// | Nanosecond  |         ns
    /// | Microsecond |         Ms
    /// | Millisecond |         ms
    /// | Second      |          s
    /// | Minute      |          m
    /// | Hour        |          h
    /// | Day         |          d
    /// | Week        |          w
    /// | Month       |          M
    /// | Year        |          y
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::DurationParserBuilder;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParserBuilder::new()
    ///         .all_time_units()
    ///         .build()
    ///         .get_current_time_units(),
    ///     vec![
    ///         NanoSecond,
    ///         MicroSecond,
    ///         MilliSecond,
    ///         Second,
    ///         Minute,
    ///         Hour,
    ///         Day,
    ///         Week,
    ///         Month,
    ///         Year
    ///     ]
    /// );
    /// ```
    pub fn all_time_units(&mut self) -> &mut Self {
        self.time_units_choice = TimeUnitsChoice::All;
        self
    }

    /// Configure the [`DurationParserBuilder`] to build the [`DurationParser`] with a custom set
    /// of time units.
    ///
    /// Setting the time units with this method overwrites any previously made choices with
    ///
    /// * [`DurationParserBuilder::default_time_units`]
    /// * [`DurationParserBuilder::all_time_units`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::DurationParserBuilder;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParserBuilder::new()
    ///         .custom_time_units(&[NanoSecond, Second, Year])
    ///         .build()
    ///         .get_current_time_units(),
    ///     vec![NanoSecond, Second, Year]
    /// );
    /// ```
    pub fn custom_time_units(&mut self, time_units: &'a [TimeUnit]) -> &mut Self {
        self.time_units_choice = TimeUnitsChoice::Custom(time_units);
        self
    }

    /// Set the default time unit to something different than [`TimeUnit::Second`]
    ///
    /// See also [`DurationParser::default_unit`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParserBuilder;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParserBuilder::new()
    ///         .all_time_units()
    ///         .default_unit(NanoSecond)
    ///         .build()
    ///         .parse("42")
    ///         .unwrap(),
    ///     Duration::new(0, 42)
    /// );
    /// ```
    pub fn default_unit(&mut self, unit: TimeUnit) -> &mut Self {
        self.config.default_unit = unit;
        self
    }

    /// Allow one or more delimiters between the number and the [`TimeUnit`].
    ///
    /// See also [`DurationParser::allow_delimiter`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParserBuilder;
    ///
    /// let parser = DurationParserBuilder::new()
    ///     .default_time_units()
    ///     .allow_delimiter(|byte| byte.is_ascii_whitespace())
    ///     .build();
    ///
    /// assert_eq!(parser.parse("123 \t\n\x0C\rns"), Ok(Duration::new(0, 123)));
    /// assert_eq!(parser.parse("123\n"), Ok(Duration::new(123, 0)));
    /// ```
    pub fn allow_delimiter(&mut self, delimiter: Delimiter) -> &mut Self {
        self.config.allow_delimiter = Some(delimiter);
        self
    }

    /// Disable parsing an exponent.
    ///
    /// See also [`DurationParser::disable_exponent`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParserBuilder, ParseError};
    ///
    /// assert_eq!(
    ///     DurationParserBuilder::new()
    ///         .default_time_units()
    ///         .disable_exponent()
    ///         .build()
    ///         .parse("123e+1"),
    ///     Err(ParseError::Syntax(3, "No exponent allowed".to_string()))
    /// );
    /// ```
    pub fn disable_exponent(&mut self) -> &mut Self {
        self.config.disable_exponent = true;
        self
    }

    /// Disable parsing a fraction in the source string.
    ///
    /// See also [`DurationParser::disable_fraction`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::{DurationParserBuilder, ParseError};
    ///
    /// let parser = DurationParserBuilder::new()
    ///     .default_time_units()
    ///     .disable_fraction()
    ///     .build();
    ///
    /// assert_eq!(
    ///     parser.parse("123.456"),
    ///     Err(ParseError::Syntax(3, "No fraction allowed".to_string()))
    /// );
    ///
    /// assert_eq!(parser.parse("123e-2"), Ok(Duration::new(1, 230_000_000)));
    /// assert_eq!(parser.parse("123ns"), Ok(Duration::new(0, 123)));
    /// ```
    pub fn disable_fraction(&mut self) -> &mut Self {
        self.config.disable_fraction = true;
        self
    }

    /// Disable parsing infinity values
    ///
    /// See also [`DurationParser::disable_infinity`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParserBuilder, ParseError};
    ///
    /// let parser = DurationParserBuilder::new().disable_infinity().build();
    ///
    /// assert_eq!(
    ///     parser.parse("inf"),
    ///     Err(ParseError::Syntax(0, format!("Invalid input: 'inf'")))
    /// );
    /// assert_eq!(
    ///     parser.parse("infinity"),
    ///     Err(ParseError::Syntax(0, format!("Invalid input: 'infinity'")))
    /// );
    /// assert_eq!(
    ///     parser.parse("+inf"),
    ///     Err(ParseError::Syntax(1, format!("Invalid input: 'inf'")))
    /// );
    /// ```
    pub fn disable_infinity(&mut self) -> &mut Self {
        self.config.disable_infinity = true;
        self
    }

    /// This setting makes a number in the source string optional.
    ///
    /// See also [`DurationParser::number_is_optional`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParserBuilder;
    ///
    /// let parser = DurationParserBuilder::new()
    ///     .default_time_units()
    ///     .number_is_optional()
    ///     .build();
    ///
    /// for input in &["ns", "e-9", "e-3Ms"] {
    ///     assert_eq!(parser.parse(input), Ok(Duration::new(0, 1)));
    /// }
    /// ```
    pub fn number_is_optional(&mut self) -> &mut Self {
        self.config.number_is_optional = true;
        self
    }

    /// Parse possibly multiple durations and sum them up.
    ///
    /// See also [`DurationParser::parse_multiple`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParserBuilder;
    ///
    /// let parser = DurationParserBuilder::new()
    ///     .default_time_units()
    ///     .parse_multiple(|byte| matches!(byte, b' ' | b'\t'))
    ///     .build();
    ///
    /// assert_eq!(parser.parse("1.5h 2e+2ns"), Ok(Duration::new(5400, 200)));
    /// assert_eq!(parser.parse("55s500ms"), Ok(Duration::new(55, 500_000_000)));
    /// assert_eq!(parser.parse("1\t1"), Ok(Duration::new(2, 0)));
    /// assert_eq!(parser.parse("1.   .1"), Ok(Duration::new(1, 100_000_000)));
    /// assert_eq!(parser.parse("2h"), Ok(Duration::new(2 * 60 * 60, 0)));
    /// assert_eq!(
    ///     parser.parse("300ms20s 5d"),
    ///     Ok(Duration::new(5 * 60 * 60 * 24 + 20, 300_000_000))
    /// );
    /// ```
    pub fn parse_multiple(&mut self, delimiter: Delimiter) -> &mut Self {
        self.config.multiple = Some(delimiter);
        self
    }

    /// Finally, build the [`DurationParser`] from this builder.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParserBuilder;
    ///
    /// let parser = DurationParserBuilder::new().default_time_units().build();
    /// for input in &["1m", "60s"] {
    ///     assert_eq!(parser.parse(input).unwrap(), Duration::new(60, 0))
    /// }
    /// ```
    pub fn build(&mut self) -> DurationParser {
        let parser = Parser::with_config(self.config.clone());

        match self.time_units_choice {
            TimeUnitsChoice::Default => DurationParser {
                time_units: TimeUnits::with_default_time_units(),
                inner: parser,
            },
            TimeUnitsChoice::All => DurationParser {
                time_units: TimeUnits::with_all_time_units(),
                inner: parser,
            },
            TimeUnitsChoice::None => DurationParser {
                time_units: TimeUnits::new(),
                inner: parser,
            },
            TimeUnitsChoice::Custom(time_units) => DurationParser {
                time_units: TimeUnits::with_time_units(time_units),
                inner: parser,
            },
        }
    }
}

/// Parse a string into a [`std::time::Duration`] by accepting a `string` similar to floating
/// point with the default set of time units.
///
/// This method is basically the same like [`DurationParser::new`] providing a simple to setup
/// onetime parser. It is generally a better idea to use the [`DurationParser`] builder if
/// multiple inputs with the same set of time units need to be parsed or a customization of the
/// time format is wished.
///
/// See also the [module level documentation](crate) for more details and more information about
/// the format.
///
/// # Errors
///
/// This function returns a [`ParseError`] when parsing of the input `string` failed.
///
/// # Examples
///
/// ```rust
/// use std::time::Duration;
///
/// use fundu::{parse_duration, ParseError};
///
/// let duration = parse_duration("+1.09e1").unwrap();
/// assert_eq!(duration, Duration::new(10, 900_000_000));
///
/// assert_eq!(
///     parse_duration("Not a number"),
///     Err(ParseError::Syntax(
///         0,
///         "Invalid input: 'Not a number'".to_string()
///     ))
/// );
/// ```
pub fn parse_duration(string: &str) -> Result<Duration, ParseError> {
    DurationParser::new().parse(string)
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;
    use crate::builder::config::Config;

    #[test]
    fn test_time_units_new() {
        let time_units = TimeUnits::new();
        assert!(time_units.data.iter().all(|t| t.is_none()));
        assert!(time_units.is_empty());
        assert_eq!(time_units.get_time_units(), vec![]);
    }

    #[test]
    fn test_time_units_with_default_time_units() {
        let time_units = TimeUnits::with_default_time_units();
        assert!(!time_units.is_empty());
        assert_eq!(time_units, TimeUnits::default());
        assert_eq!(
            time_units.get_time_units(),
            vec![
                NanoSecond,
                MicroSecond,
                MilliSecond,
                Second,
                Minute,
                Hour,
                Day,
                Week
            ]
        );
    }

    #[test]
    fn test_time_units_with_all_time_units() {
        let time_units = TimeUnits::with_all_time_units();
        assert!(!time_units.is_empty());
        assert_eq!(
            time_units.get_time_units(),
            vec![
                NanoSecond,
                MicroSecond,
                MilliSecond,
                Second,
                Minute,
                Hour,
                Day,
                Week,
                Month,
                Year
            ]
        );
    }

    #[test]
    fn test_time_units_with_time_units() {
        let time_units = TimeUnits::with_time_units(&[NanoSecond]);
        assert!(!time_units.is_empty());
        assert_eq!(time_units.get_time_units(), vec![NanoSecond,]);
    }

    #[rstest]
    #[case::nano_second(NanoSecond, "ns")]
    #[case::micro_second(MicroSecond, "Ms")]
    #[case::milli_second(MilliSecond, "ms")]
    #[case::second(Second, "s")]
    #[case::minute(Minute, "m")]
    #[case::hour(Hour, "h")]
    #[case::day(Day, "d")]
    #[case::week(Week, "w")]
    #[case::month(Month, "M")]
    #[case::year(Year, "y")]
    fn test_time_units_add_time_unit_when_empty(
        #[case] time_unit: TimeUnit,
        #[case] identifier: &str,
    ) {
        let mut time_units = TimeUnits::new();
        time_units.add_time_unit(time_unit);
        assert_eq!(time_units.get_time_units(), vec![time_unit]);
        assert_eq!(
            time_units.get(identifier),
            Some((time_unit, Multiplier(1, 0)))
        );
    }

    #[test]
    fn test_time_units_add_time_unit_twice() {
        let mut time_units = TimeUnits::new();
        let time_unit = MicroSecond;

        time_units.add_time_unit(time_unit);
        time_units.add_time_unit(time_unit);

        assert_eq!(time_units.get_time_units(), vec![time_unit]);
    }

    #[test]
    fn test_time_units_when_empty_then_return_true() {
        assert!(TimeUnits::new().is_empty())
    }

    #[rstest]
    fn test_time_units_is_empty_when_not_empty_then_return_false(
        #[values(
            NanoSecond,
            MicroSecond,
            MilliSecond,
            Second,
            Minute,
            Hour,
            Day,
            Week,
            Month,
            Year
        )]
        time_unit: TimeUnit,
    ) {
        let time_units = TimeUnits::with_time_units(&[time_unit]);
        assert!(!time_units.is_empty());
    }

    #[test]
    fn test_time_units_add_time_units_when_in_order() {
        let mut time_units = TimeUnits::new();
        let units = &[NanoSecond, Second, Month];
        time_units.add_time_units(units);
        assert_eq!(time_units.get_time_units(), units);
    }

    #[test]
    fn test_time_units_add_time_units_when_not_in_order() {
        let mut time_units = TimeUnits::new();
        let mut units = [Month, Second, Hour, NanoSecond];
        time_units.add_time_units(&units);
        units.sort();
        assert_eq!(time_units.get_time_units(), &units);
    }

    #[rstest]
    #[case::nano_second("ns", Some((NanoSecond, Multiplier(1,0))))]
    #[case::micro_second("Ms", Some((MicroSecond, Multiplier(1,0))))]
    #[case::milli_second("ms", Some((MilliSecond, Multiplier(1,0))))]
    #[case::second("s", Some((Second, Multiplier(1,0))))]
    #[case::minute("m", Some((Minute, Multiplier(1,0))))]
    #[case::hour("h", Some((Hour, Multiplier(1,0))))]
    #[case::day("d", Some((Day, Multiplier(1,0))))]
    #[case::week("w", Some((Week, Multiplier(1,0))))]
    #[case::month("M", Some((Month, Multiplier(1,0))))]
    #[case::year("y", Some((Year, Multiplier(1,0))))]
    fn test_time_units_get(#[case] id: &str, #[case] expected: Option<(TimeUnit, Multiplier)>) {
        assert_eq!(TimeUnits::with_all_time_units().get(id), expected);
        assert_eq!(TimeUnits::new().get(id), None);
    }

    #[test]
    fn test_time_units_get_time_units() {
        let time_units = TimeUnits::with_all_time_units();
        assert_eq!(
            time_units.get_time_units(),
            vec![
                NanoSecond,
                MicroSecond,
                MilliSecond,
                Second,
                Minute,
                Hour,
                Day,
                Week,
                Month,
                Year
            ]
        )
    }

    #[test]
    fn test_duration_parser_init_when_default() {
        let config = Config::new();
        let parser = DurationParser::default();
        assert_eq!(parser.inner.config, config);
        assert_eq!(
            parser.get_current_time_units(),
            vec![
                NanoSecond,
                MicroSecond,
                MilliSecond,
                Second,
                Minute,
                Hour,
                Day,
                Week
            ]
        )
    }

    #[test]
    fn test_duration_parser_setting_allow_delimiter() {
        let mut parser = DurationParser::new();
        parser.allow_delimiter(Some(|byte| byte == b' '));
        assert!(parser.inner.config.allow_delimiter.unwrap()(b' '));
    }

    #[test]
    fn test_duration_parser_setting_disable_infinity() {
        let mut expected = Config::new();
        expected.disable_infinity = true;
        let mut parser = DurationParser::new();

        parser.disable_infinity(true);

        assert_eq!(parser.inner.config, expected);
    }

    #[test]
    fn test_duration_parser_setting_parse_multiple() {
        let delimiter = |byte: u8| byte.is_ascii_whitespace();
        let mut expected = Config::new();
        expected.multiple = Some(delimiter);

        let mut parser = DurationParser::new();
        parser.parse_multiple(Some(delimiter));

        assert_eq!(parser.inner.config, expected);
    }

    #[cfg(feature = "negative")]
    #[test]
    fn test_duration_parser_parse_negative_calls_parser() {
        let parser = DurationParser::new();
        assert_eq!(parser.inner.config, Config::new());
        assert_eq!(
            parser.parse_negative("1y"),
            Err(ParseError::TimeUnit(
                1,
                "Invalid time unit: 'y'".to_string()
            ))
        );
        assert_eq!(
            parser.parse_negative("-1.0e0ns"),
            Ok(time::Duration::new(0, -1))
        )
    }

    #[test]
    fn test_duration_parser_when_builder() {
        assert_eq!(DurationParser::builder(), DurationParserBuilder::new());
    }

    #[test]
    fn test_duration_parser_builder_when_default() {
        assert_eq!(
            DurationParserBuilder::default(),
            DurationParserBuilder::new()
        );
    }

    #[test]
    fn test_duration_parser_builder_when_new() {
        let builder = DurationParserBuilder::new();
        assert_eq!(builder.config, Config::new());
        assert_eq!(builder.time_units_choice, TimeUnitsChoice::None);
    }

    #[test]
    fn test_duration_parser_builder_when_default_time_units() {
        let mut builder = DurationParserBuilder::new();
        builder.default_time_units();
        assert_eq!(builder.time_units_choice, TimeUnitsChoice::Default);
    }

    #[test]
    fn test_duration_parser_builder_when_all_time_units() {
        let mut builder = DurationParserBuilder::new();
        builder.all_time_units();
        assert_eq!(builder.time_units_choice, TimeUnitsChoice::All);
    }

    #[test]
    fn test_duration_parser_builder_when_custom_time_units() {
        let mut builder = DurationParserBuilder::new();
        builder.custom_time_units(&[MicroSecond, Hour, Week, Year]);
        assert_eq!(
            builder.time_units_choice,
            TimeUnitsChoice::Custom(&[MicroSecond, Hour, Week, Year])
        );
    }

    #[test]
    fn test_duration_parser_builder_when_default_unit() {
        let mut expected = Config::new();
        expected.default_unit = MicroSecond;

        let mut builder = DurationParserBuilder::new();
        builder.default_unit(MicroSecond);

        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_duration_parser_builder_when_allow_delimiter() {
        let mut builder = DurationParserBuilder::new();
        builder.allow_delimiter(|b| b == b' ');

        assert!(builder.config.allow_delimiter.unwrap()(b' '));
    }

    #[test]
    fn test_duration_parser_builder_when_disable_fraction() {
        let mut expected = Config::new();
        expected.disable_fraction = true;

        let mut builder = DurationParserBuilder::new();
        builder.disable_fraction();

        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_duration_parser_builder_when_disable_exponent() {
        let mut expected = Config::new();
        expected.disable_exponent = true;

        let mut builder = DurationParserBuilder::new();
        builder.disable_exponent();

        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_duration_parser_builder_when_disable_infinity() {
        let mut expected = Config::new();
        expected.disable_infinity = true;

        let mut builder = DurationParserBuilder::new();
        builder.disable_infinity();

        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_duration_parser_builder_when_number_is_optional() {
        let mut expected = Config::new();
        expected.number_is_optional = true;

        let mut builder = DurationParserBuilder::new();
        builder.number_is_optional();

        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_duration_parser_builder_when_parse_multiple() {
        let delimiter = |byte: u8| byte.is_ascii_whitespace();
        let mut expected = Config::new();
        expected.multiple = Some(delimiter);

        let mut builder = DurationParserBuilder::new();
        builder.parse_multiple(delimiter);

        assert_eq!(builder.config, expected);
    }

    #[rstest]
    #[case::default_time_units(TimeUnitsChoice::Default, DurationParser::new())]
    #[case::all_time_units(TimeUnitsChoice::All, DurationParser::with_all_time_units())]
    #[case::no_time_units(TimeUnitsChoice::None, DurationParser::without_time_units())]
    #[case::custom_time_units(
            TimeUnitsChoice::Custom(&[NanoSecond, Minute]),
            DurationParser::with_time_units(&[NanoSecond, Minute])
    )]
    fn test_duration_parser_builder_build(
        #[case] choice: TimeUnitsChoice,
        #[case] expected: DurationParser,
    ) {
        let mut builder = DurationParserBuilder::new();
        builder.time_units_choice = choice;

        assert_eq!(builder.build(), expected);
    }
}
