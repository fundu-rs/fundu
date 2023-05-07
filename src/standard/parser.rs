// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration as StdDuration;

use super::time_units::TimeUnits;
use crate::config::Delimiter;
use crate::parse::Parser;
use crate::time::Duration as FunduDuration;
use crate::{DurationParserBuilder, ParseError, TimeUnit};

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
/// use fundu::{Duration, DurationParser};
///
/// let parser = DurationParser::new();
/// assert_eq!(parser.parse("42Ms").unwrap(), Duration::positive(0, 42_000));
/// ```
///
/// The parser is reusable and the set of time units is fully customizable
///
///
/// ```rust
/// use fundu::{Duration, DurationParser, TimeUnit::*};
//
/// let parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);
/// for (input, expected) in &[
///     ("9e3ns", Duration::positive(0, 9000)),
///     ("10m", Duration::positive(600, 0)),
///     ("1.1h", Duration::positive(3960, 0)),
///     ("7", Duration::positive(7, 0)),
/// ] {
///     assert_eq!(parser.parse(input).unwrap(), *expected);
/// }
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct DurationParser {
    pub(super) time_units: TimeUnits,
    pub(super) inner: Parser,
}

impl DurationParser {
    /// Construct the parser with the default set of [`TimeUnit`]s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{Duration, DurationParser};
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse("1").unwrap(),
    ///     Duration::positive(1, 0)
    /// );
    /// assert_eq!(
    ///     DurationParser::new().parse("1s").unwrap(),
    ///     Duration::positive(1, 0)
    /// );
    /// assert_eq!(
    ///     DurationParser::new().parse("42.0e9ns").unwrap(),
    ///     Duration::positive(42, 0)
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
    /// use fundu::TimeUnit::*;
    /// use fundu::{Duration, DurationParser};
    ///
    /// assert_eq!(
    ///     DurationParser::with_time_units(&[NanoSecond, Hour, Week])
    ///         .parse("1.5w")
    ///         .unwrap(),
    ///     Duration::positive(60 * 60 * 24 * 7 + 60 * 60 * 24 * 7 / 2, 0)
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
    /// use fundu::{Duration, DurationParser};
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units().parse("33.33").unwrap(),
    ///     Duration::positive(33, 330_000_000)
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
    /// use fundu::TimeUnit::*;
    /// use fundu::{Duration, DurationParser};
    ///
    /// let parser = DurationParser::builder()
    ///     .all_time_units()
    ///     .default_unit(MicroSecond)
    ///     .allow_delimiter(|byte| byte.is_ascii_whitespace())
    ///     .build();
    ///
    /// assert_eq!(parser.parse("1 \t\nns").unwrap(), Duration::positive(0, 1));
    /// assert_eq!(parser.parse("1").unwrap(), Duration::positive(0, 1_000));
    ///
    /// // instead of
    ///
    /// let mut parser = DurationParser::with_all_time_units();
    /// parser
    ///     .default_unit(MicroSecond)
    ///     .allow_delimiter(Some(|byte| byte == b' '));
    ///
    /// assert_eq!(parser.parse("1 ns").unwrap(), Duration::positive(0, 1));
    /// assert_eq!(parser.parse("1").unwrap(), Duration::positive(0, 1_000));
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
    /// use fundu::{Duration, DurationParser};
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse("1.2e-1s").unwrap(),
    ///     Duration::positive(0, 120_000_000),
    /// );
    /// ```
    #[inline]
    pub fn parse(&self, source: &str) -> Result<FunduDuration, ParseError> {
        self.inner.parse(source, &self.time_units, None)
    }

    /// Set the default [`TimeUnit`] to `unit`.
    ///
    /// The default time unit is applied when no time unit was given in the input string. If the
    /// default time unit is not set with this method the parser defaults to [`TimeUnit::Second`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{Duration, DurationParser};
    ///
    /// assert_eq!(
    ///     DurationParser::with_all_time_units()
    ///         .default_unit(NanoSecond)
    ///         .parse("42")
    ///         .unwrap(),
    ///     Duration::positive(0, 42)
    /// );
    /// ```
    pub fn default_unit(&mut self, unit: TimeUnit) -> &mut Self {
        self.inner.config.default_unit = unit;
        self
    }

    /// If `Some`, allow one or more [`Delimiter`] between the number and the [`TimeUnit`].
    ///
    /// A [`Delimiter`] is defined as closure taking a byte and returning true if the delimiter
    /// matched. Per default no delimiter is allowed between the number and the [`TimeUnit`]. As
    /// usual the default time unit is assumed if no time unit was present.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{Duration, DurationParser, ParseError};
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
    /// assert_eq!(parser.parse("123 ns"), Ok(Duration::positive(0, 123)));
    /// assert_eq!(parser.parse("123    ns"), Ok(Duration::positive(0, 123)));
    /// assert_eq!(parser.parse("123ns"), Ok(Duration::positive(0, 123)));
    ///
    /// parser.allow_delimiter(Some(|byte| matches!(byte, b'\t' | b'\n' | b'\r' | b' ')));
    /// assert_eq!(parser.parse("123\r\nns"), Ok(Duration::positive(0, 123)));
    /// assert_eq!(parser.parse("123\t\n\r ns"), Ok(Duration::positive(0, 123)));
    /// ```
    pub fn allow_delimiter(&mut self, delimiter: Option<Delimiter>) -> &mut Self {
        self.inner.config.allow_delimiter = delimiter;
        self
    }

    pub fn allow_negative(&mut self, value: bool) -> &mut Self {
        self.inner.config.allow_negative = value;
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
    /// use fundu::{Duration, DurationParser, ParseError};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.disable_fraction(true);
    ///
    /// assert_eq!(
    ///     parser.parse("123.456"),
    ///     Err(ParseError::Syntax(3, "No fraction allowed".to_string()))
    /// );
    ///
    /// assert_eq!(
    ///     parser.parse("123e-2"),
    ///     Ok(Duration::positive(1, 230_000_000))
    /// );
    ///
    /// assert_eq!(parser.parse("123ns"), Ok(Duration::positive(0, 123)));
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
    /// use fundu::{Duration, DurationParser};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.number_is_optional(true);
    ///
    /// for input in &["ns", "e-9", "e-3Ms"] {
    ///     assert_eq!(parser.parse(input), Ok(Duration::positive(0, 1)));
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
    /// use fundu::{Duration, DurationParser};
    ///
    /// let delimiter = |byte| matches!(byte, b' ' | b'\t');
    /// let mut parser = DurationParser::new();
    /// parser
    ///     .parse_multiple(Some(delimiter))
    ///     .number_is_optional(true);
    ///
    /// // Here, the parser parses `1`, `s`, `1` and then `ns` separately
    /// assert_eq!(parser.parse("1 s 1 ns"), Ok(Duration::positive(3, 1)));
    ///
    /// // Here, the parser parses `1 s` and then `1 ns`.
    /// parser.allow_delimiter(Some(delimiter));
    /// assert_eq!(parser.parse("1 s 1 ns"), Ok(Duration::positive(1, 1)));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{Duration, DurationParser};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.parse_multiple(Some(|byte| matches!(byte, b' ' | b'\t')));
    ///
    /// assert_eq!(
    ///     parser.parse("1.5h 2e+2ns"),
    ///     Ok(Duration::positive(5400, 200))
    /// );
    /// assert_eq!(
    ///     parser.parse("55s500ms"),
    ///     Ok(Duration::positive(55, 500_000_000))
    /// );
    /// assert_eq!(parser.parse("1\t1"), Ok(Duration::positive(2, 0)));
    /// assert_eq!(
    ///     parser.parse("1.   .1"),
    ///     Ok(Duration::positive(1, 100_000_000))
    /// );
    /// assert_eq!(parser.parse("2h"), Ok(Duration::positive(2 * 60 * 60, 0)));
    /// assert_eq!(
    ///     parser.parse("300ms20s 5d"),
    ///     Ok(Duration::positive(5 * 60 * 60 * 24 + 20, 300_000_000))
    /// );
    /// ```
    pub fn parse_multiple(&mut self, delimiter: Option<Delimiter>) -> &mut Self {
        self.inner.config.parse_multiple = delimiter;
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
pub fn parse_duration(string: &str) -> Result<StdDuration, ParseError> {
    DurationParser::new()
        .parse(string)
        // unwrap is safe here because negative durations aren't allowed in the default
        // configuration of the DurationParser
        .map(|d| d.try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::Config;
    use crate::TimeUnit::*;

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
        let mut parser = DurationParser::new();
        parser.parse_multiple(Some(|byte: u8| byte == 0xff));

        assert!(parser.inner.config.parse_multiple.unwrap()(0xff));
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
}
