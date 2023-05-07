// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use super::time_units::{CustomTimeUnits, Identifiers, TimeKeyword};
use crate::config::{Config, DEFAULT_CONFIG};
use crate::parse::Parser;
use crate::{CustomDurationParser, CustomTimeUnit, Delimiter, TimeUnit};

/// Like [`crate::DurationParserBuilder`] for [`crate::DurationParser`], this is a builder for a
/// [`CustomDurationParser`].
///
/// # Examples
///
/// ```rust
/// use fundu::TimeUnit::*;
/// use fundu::{CustomDurationParser, CustomDurationParserBuilder, Duration};
///
/// let parser = CustomDurationParserBuilder::new()
///     .time_units(&[(NanoSecond, &["ns"])])
///     .default_unit(MicroSecond)
///     .allow_delimiter(|byte| byte == b' ')
///     .build();
///
/// assert_eq!(parser.parse("1 ns").unwrap(), Duration::positive(0, 1));
/// assert_eq!(parser.parse("1").unwrap(), Duration::positive(0, 1_000));
///
/// // instead of
///
/// let mut parser = CustomDurationParser::with_time_units(&[(NanoSecond, &["ns"])]);
/// parser
///     .default_unit(MicroSecond)
///     .allow_delimiter(Some(|byte| byte == b' '));
///
/// assert_eq!(parser.parse("1 ns").unwrap(), Duration::positive(0, 1));
/// assert_eq!(parser.parse("1").unwrap(), Duration::positive(0, 1_000));
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct CustomDurationParserBuilder<'a> {
    config: Config,
    time_units: Option<&'a [Identifiers<'a>]>,
    custom_time_units: Vec<CustomTimeUnit<'a>>,
    keywords: Vec<TimeKeyword<'a>>,
}

impl<'a> Default for CustomDurationParserBuilder<'a> {
    /// Construct a new [`CustomDurationParserBuilder`] without any time units.
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> CustomDurationParserBuilder<'a> {
    /// Construct a new [`CustomDurationParserBuilder`].
    ///
    /// Per default there are no time units configured in the builder. Use
    /// [`CustomDurationParserBuilder::time_units`] to add time units.
    ///
    /// Unlike its counterpart [`crate::DurationParserBuilder`], this builder is not reusable and
    /// [`CustomDurationParserBuilder::build`] consumes this builder. This is due to the more
    /// complicated structure of custom time units and to keep the building process as performant
    /// as possible.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParser, CustomDurationParserBuilder};
    ///
    /// assert_eq!(
    ///     CustomDurationParserBuilder::new().build(),
    ///     CustomDurationParser::new()
    /// );
    /// ```
    pub const fn new() -> Self {
        Self {
            config: DEFAULT_CONFIG,
            time_units: None,
            custom_time_units: vec![],
            keywords: vec![],
        }
    }

    /// Let's the [`CustomDurationParserBuilder`] build the [`CustomDurationParser`] with a set of
    /// time units.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, Multiplier};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&[
    ///         (NanoSecond, &["ns"]),
    ///         (Second, &["s", "sec", "secs"]),
    ///         (Year, &["year"]),
    ///     ])
    ///     .build();
    ///
    /// assert_eq!(
    ///     parser.get_time_unit_by_id("ns"),
    ///     Some((NanoSecond, Multiplier(1, 0)))
    /// );
    /// assert_eq!(
    ///     parser.get_time_unit_by_id("s"),
    ///     Some((Second, Multiplier(1, 0)))
    /// );
    /// assert_eq!(
    ///     parser.get_time_unit_by_id("year"),
    ///     Some((Year, Multiplier(1, 0)))
    /// );
    /// ```
    pub const fn time_units(mut self, time_units: &'a [Identifiers<'a>]) -> Self {
        self.time_units = Some(time_units);
        self
    }

    /// Add a custom time unit to the current set of [`TimeUnit`]s.
    ///
    /// See also [`CustomDurationParser`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, CustomTimeUnit, Duration, Multiplier};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .custom_time_unit(CustomTimeUnit::new(
    ///         Week,
    ///         &["fortnight", "fortnights"],
    ///         Some(Multiplier(2, 0)),
    ///     ))
    ///     .build();
    /// assert_eq!(
    ///     parser.parse("1fortnight").unwrap(),
    ///     Duration::positive(2 * 7 * 24 * 60 * 60, 0),
    /// );
    /// ```
    pub fn custom_time_unit(mut self, time_unit: CustomTimeUnit<'a>) -> Self {
        self.custom_time_units.push(time_unit);
        self
    }

    /// Add multiple [`CustomTimeUnit`]s at once.
    ///
    /// See also [`CustomDurationParser::custom_time_units`]
    ///
    /// # Example
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, CustomTimeUnit, Duration, Multiplier};
    ///
    /// const CUSTOM_TIME_UNITS: [CustomTimeUnit; 2] = [
    ///     CustomTimeUnit::new(Week, &["fortnight", "fortnights"], Some(Multiplier(2, 0))),
    ///     CustomTimeUnit::new(Second, &["shake", "shakes"], Some(Multiplier(1, -8))),
    /// ];
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .custom_time_units(&CUSTOM_TIME_UNITS)
    ///     .build();
    ///
    /// assert_eq!(
    ///     parser.parse("1fortnight").unwrap(),
    ///     Duration::positive(2 * 7 * 24 * 60 * 60, 0),
    /// );
    /// ```
    pub fn custom_time_units(mut self, time_units: &[CustomTimeUnit<'a>]) -> Self {
        for unit in time_units {
            self.custom_time_units.push(*unit);
        }
        self
    }

    pub fn keyword(mut self, keyword: TimeKeyword<'a>) -> Self {
        self.keywords.push(keyword);
        self
    }

    pub fn keywords(mut self, keywords: &[TimeKeyword<'a>]) -> Self {
        for keyword in keywords {
            self.keywords.push(*keyword);
        }
        self
    }

    /// Set the default time unit to a [`TimeUnit`] different than [`TimeUnit::Second`]
    ///
    /// See also [`crate::DurationParser::default_unit`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, Duration};
    ///
    /// assert_eq!(
    ///     CustomDurationParserBuilder::new()
    ///         .default_unit(NanoSecond)
    ///         .build()
    ///         .parse("42")
    ///         .unwrap(),
    ///     Duration::positive(0, 42)
    /// );
    /// ```
    pub const fn default_unit(mut self, unit: TimeUnit) -> Self {
        self.config.default_unit = unit;
        self
    }

    /// Allow one or more delimiters between the number and the [`TimeUnit`].
    ///
    /// See also [`crate::DurationParser::allow_delimiter`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, Duration};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&[(NanoSecond, &["ns"])])
    ///     .allow_delimiter(|byte| byte == b' ')
    ///     .build();
    ///
    /// assert_eq!(parser.parse("123 ns"), Ok(Duration::positive(0, 123)));
    /// assert_eq!(parser.parse("123 "), Ok(Duration::positive(123, 0)));
    /// ```
    pub const fn allow_delimiter(mut self, delimiter: Delimiter) -> Self {
        self.config.allow_delimiter = Some(delimiter);
        self
    }

    pub const fn allow_negative(mut self) -> Self {
        self.config.allow_negative = true;
        self
    }

    pub const fn allow_ago(mut self, delimiter: Delimiter) -> Self {
        self.config.allow_ago = Some(delimiter);
        self.config.allow_negative = true;
        self
    }

    /// Disable parsing an exponent.
    ///
    /// See also [`crate::DurationParser::disable_exponent`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParserBuilder, ParseError};
    ///
    /// assert_eq!(
    ///     CustomDurationParserBuilder::new()
    ///         .disable_exponent()
    ///         .build()
    ///         .parse("123e+1"),
    ///     Err(ParseError::Syntax(3, "No exponent allowed".to_string()))
    /// );
    /// ```
    pub const fn disable_exponent(mut self) -> Self {
        self.config.disable_exponent = true;
        self
    }

    /// Disable parsing a fraction in the source string.
    ///
    /// See also [`crate::DurationParser::disable_fraction`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, Duration, ParseError};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&[(NanoSecond, &["ns"])])
    ///     .disable_fraction()
    ///     .build();
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
    /// assert_eq!(parser.parse("123ns"), Ok(Duration::positive(0, 123)));
    /// ```
    pub const fn disable_fraction(mut self) -> Self {
        self.config.disable_fraction = true;
        self
    }

    /// Disable parsing infinity values
    ///
    /// See also [`crate::DurationParser::disable_infinity`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParserBuilder, ParseError};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .disable_infinity()
    ///     .build();
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
    pub const fn disable_infinity(mut self) -> Self {
        self.config.disable_infinity = true;
        self
    }

    /// This setting makes a number in the source string optional.
    ///
    /// See also [`crate::DurationParser::number_is_optional`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParserBuilder, Duration, DEFAULT_TIME_UNITS};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&DEFAULT_TIME_UNITS)
    ///     .number_is_optional()
    ///     .build();
    ///
    /// for input in &[".001e-6s", "ns", "e-9", "e-3Ms"] {
    ///     assert_eq!(parser.parse(input), Ok(Duration::positive(0, 1)));
    /// }
    /// ```
    pub const fn number_is_optional(mut self) -> Self {
        self.config.number_is_optional = true;
        self
    }

    /// Parse possibly multiple durations and sum them up.
    ///
    /// See also [`crate::DurationParser::parse_multiple`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParserBuilder, Duration, DEFAULT_TIME_UNITS};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&DEFAULT_TIME_UNITS)
    ///     .parse_multiple(|byte| matches!(byte, b' ' | b'\t'))
    ///     .build();
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
    pub const fn parse_multiple(mut self, delimiter: Delimiter) -> Self {
        self.config.parse_multiple = Some(delimiter);
        self
    }

    /// Finally, build the [`CustomDurationParser`] from this builder.
    ///
    /// Note this method is meant as a one-off builder method and can therefore only be used once
    /// on each [`CustomDurationParserBuilder`]. However, the parser built with this method
    /// can be used multiple times.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, Duration};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&[(Minute, &["min"]), (Hour, &["h", "hr"])])
    ///     .allow_delimiter(|byte| matches!(byte, b'\t' | b'\n' | b'\r' | b' '))
    ///     .build();
    ///
    /// for input in &["60 min", "1h", "1\t\n hr"] {
    ///     assert_eq!(parser.parse(input).unwrap(), Duration::positive(60 * 60, 0));
    /// }
    /// ```
    pub fn build(self) -> CustomDurationParser<'a> {
        let parser = Parser::with_config(self.config);
        let mut parser = match &self.time_units {
            Some(time_units) => CustomDurationParser {
                time_units: CustomTimeUnits::with_time_units(time_units),
                inner: parser,
                keywords: CustomTimeUnits::with_capacity(self.keywords.len()),
            },
            None => CustomDurationParser {
                time_units: CustomTimeUnits::with_capacity(self.custom_time_units.len()),
                inner: parser,
                keywords: CustomTimeUnits::with_capacity(self.keywords.len()),
            },
        };
        parser.custom_time_units(&self.custom_time_units);
        parser.keywords(&self.keywords);
        parser
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::config::Config;
    use crate::TimeUnit::*;
    use crate::{CustomTimeUnit, Multiplier};

    #[test]
    fn test_custom_duration_parser_builder_when_default() {
        assert_eq!(
            CustomDurationParserBuilder::default(),
            CustomDurationParserBuilder::new()
        );
    }

    #[test]
    fn test_custom_duration_parser_builder_when_new() {
        let builder = CustomDurationParserBuilder::new();
        assert_eq!(builder.config, Config::new());
        assert!(builder.time_units.is_none());
        assert!(builder.custom_time_units.is_empty());
    }

    #[test]
    fn test_custom_duration_parser_builder_when_default_unit() {
        let mut expected = Config::new();
        expected.default_unit = MicroSecond;

        let builder = CustomDurationParserBuilder::new().default_unit(MicroSecond);
        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_custom_duration_parser_builder_when_allow_delimiter() {
        let builder = CustomDurationParserBuilder::new().allow_delimiter(|byte| byte == b' ');
        assert!(builder.config.allow_delimiter.unwrap()(b' '));
    }

    #[test]
    fn test_custom_duration_parser_builder_when_disable_exponent() {
        let mut expected = Config::new();
        expected.disable_exponent = true;

        let builder = CustomDurationParserBuilder::new().disable_exponent();
        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_custom_duration_parser_builder_when_disable_fraction() {
        let mut expected = Config::new();
        expected.disable_fraction = true;

        let builder = CustomDurationParserBuilder::new().disable_fraction();
        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_custom_duration_parser_builder_when_disable_infinity() {
        let mut expected = Config::new();
        expected.disable_infinity = true;

        let builder = CustomDurationParserBuilder::new().disable_infinity();
        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_custom_duration_parser_builder_when_number_is_optional() {
        let mut expected = Config::new();
        expected.number_is_optional = true;

        let builder = CustomDurationParserBuilder::new().number_is_optional();
        assert_eq!(builder.config, expected);
    }

    #[test]
    fn test_custom_duration_parser_builder_when_parse_multiple() {
        let builder = CustomDurationParserBuilder::new().parse_multiple(|byte| byte == 0xff);
        assert!(builder.config.parse_multiple.unwrap()(0xff));
    }

    #[test]
    fn test_custom_duration_parser_builder_when_build_with_regular_time_units() {
        let mut expected = Config::new();
        expected.number_is_optional = true;
        let parser = CustomDurationParserBuilder::new()
            .time_units(&[(Second, &["s", "secs"])])
            .custom_time_unit(CustomTimeUnit::new(Hour, &["h"], Some(Multiplier(3, 0))))
            .custom_time_units(&[
                CustomTimeUnit::new(Minute, &["m", "min"], Some(Multiplier(2, 0))),
                CustomTimeUnit::new(Day, &["d"], Some(Multiplier(4, 0))),
            ])
            .number_is_optional()
            .build();
        assert!(!parser.is_empty());
        assert_eq!(
            parser.get_time_unit_by_id("s"),
            Some((Second, Multiplier(1, 0)))
        );
        assert_eq!(
            parser.get_time_unit_by_id("secs"),
            Some((Second, Multiplier(1, 0)))
        );
        assert_eq!(
            parser.get_time_unit_by_id("h"),
            Some((Hour, Multiplier(3, 0)))
        );
        assert_eq!(
            parser.get_time_unit_by_id("m"),
            Some((Minute, Multiplier(2, 0)))
        );
        assert_eq!(
            parser.get_time_unit_by_id("min"),
            Some((Minute, Multiplier(2, 0)))
        );
        assert_eq!(
            parser.get_time_unit_by_id("d"),
            Some((Day, Multiplier(4, 0)))
        );
    }

    #[test]
    fn test_custom_duration_parser_builder_when_build_without_regular_time_units() {
        let mut expected = Config::new();
        expected.number_is_optional = true;
        let parser = CustomDurationParserBuilder::new()
            .custom_time_units(&[
                CustomTimeUnit::new(Minute, &["m", "min"], Some(Multiplier(2, 0))),
                CustomTimeUnit::new(Day, &["d"], Some(Multiplier(4, 0))),
            ])
            .number_is_optional()
            .build();
        assert!(!parser.is_empty());
        assert_eq!(
            parser.get_time_unit_by_id("m"),
            Some((Minute, Multiplier(2, 0)))
        );
        assert_eq!(
            parser.get_time_unit_by_id("min"),
            Some((Minute, Multiplier(2, 0)))
        );
        assert_eq!(
            parser.get_time_unit_by_id("d"),
            Some((Day, Multiplier(4, 0)))
        );
    }
}
