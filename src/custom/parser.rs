// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use super::builder::CustomDurationParserBuilder;
use super::time_units::{CustomTimeUnit, CustomTimeUnits, IdentifiersSlice};
use crate::parse::Parser;
use crate::time::{Multiplier, TimeUnitsLike};
use crate::{Delimiter, ParseError, TimeUnit};

/// A parser with a customizable set of [`TimeUnit`]s and customizable identifiers.
///
/// See also [`CustomDurationParser::with_time_units`]. See
/// [`CustomDurationParser::custom_time_unit`] to define completely new time units.
///
/// # Problems
///
/// It's possible to choose identifiers very freely within the `utf-8` range. However, some
/// identifiers interact badly with the parser and may lead to unexpected results if they
/// start with:
///
/// * `e` or `E` which is also indicating an exponent. If [`CustomDurationParser::disable_exponent`]
/// is set to true this problem does not occur.
/// * `inf` and in consequence `infinity` (lowercase and uppercase). These are reserved words as
/// long as [`CustomDurationParser::disable_infinity`] isn't set to true.
/// * ascii digits from `0` to `9`
/// * `.` which is also indicating a fraction. If [`CustomDurationParser::disable_fraction`] is set
/// to true, this problem does not occur
/// * `+`, `-` which are in use for signs.
/// * whitespace characters
#[derive(Debug, PartialEq, Eq)]
pub struct CustomDurationParser<'a> {
    pub(super) time_units: CustomTimeUnits<'a>,
    pub(super) inner: Parser,
}

impl<'a> CustomDurationParser<'a> {
    /// Create a new empty [`CustomDurationParser`] without any time units.
    ///
    /// There's also [`CustomDurationParser::with_time_units`] which initializes the parser with a
    /// set time units with custom `ids`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::CustomDurationParser;
    ///
    /// assert_eq!(
    ///     CustomDurationParser::new().parse("100.0").unwrap(),
    ///     Duration::new(100, 0)
    /// );
    /// ```
    pub fn new() -> Self {
        Self {
            time_units: CustomTimeUnits::new(),
            inner: Parser::new(),
        }
    }

    /// Create a new [`CustomDurationParser`] with an initial set of custom identifiers for each
    /// [`TimeUnit`]s in `units`.
    ///
    /// Not all time units need to be defined, so if there is no intention to include a specific
    /// [`TimeUnit`] just leave it out of the `units`. Be aware, that this method does not check
    /// the validity of identifiers, so besides the need to be a valid `utf-8` sequence there
    /// are no other hard limitations but see also the `Problems` section in
    /// [`CustomDurationParser`]. There is also no check for duplicate `ids` but empty `ids`
    /// are ignored. Note the ids for time units are case sensitive.
    ///
    /// You may find it helpful to start with a pre-defined custom sets of [`TimeUnit`]:
    /// * [`SYSTEMD_TIME_UNITS`]: This is the set of time units as specified in the [`systemd.time`](https://www.man7.org/linux/man-pages/man7/systemd.time.7.html)
    ///   documentation
    /// * [`DEFAULT_TIME_UNITS`]: This is the complete set of time units with their default ids as
    ///   used the standard crate by [`crate::DurationParser`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, Multiplier};
    ///
    /// let parser = CustomDurationParser::with_time_units(&[
    ///     (Second, &["s"]),
    ///     (Minute, &["Min"]),
    ///     (Hour, &["ώρα"]),
    /// ]);
    /// assert_eq!(
    ///     parser.get_time_unit_by_id("s"),
    ///     Some((Second, Multiplier(1, 0)))
    /// );
    /// assert_eq!(
    ///     parser.get_time_unit_by_id("Min"),
    ///     Some((Minute, Multiplier(1, 0)))
    /// );
    /// assert_eq!(
    ///     parser.get_time_unit_by_id("ώρα"),
    ///     Some((Hour, Multiplier(1, 0)))
    /// );
    ///
    /// assert!(parser.parse("42.0min").is_err()); // Note the small letter `m` instead of `M`
    ///
    /// assert_eq!(parser.parse("42e-1ώρα").unwrap(), Duration::new(15120, 0));
    /// ```
    pub fn with_time_units(units: &'a [IdentifiersSlice<'a>]) -> Self {
        Self {
            time_units: CustomTimeUnits::with_time_units(units),
            inner: Parser::new(),
        }
    }

    /// Use the [`CustomDurationParserBuilder`] to construct a [`CustomDurationParser`].
    ///
    /// The [`CustomDurationParserBuilder`] is more ergonomic in some use cases than using
    /// [`CustomDurationParser`] directly. Using this method is the same like invoking
    /// [`CustomDurationParserBuilder::default`].
    ///
    /// See [`CustomDurationParserBuilder`] for more details.
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
    ///     .allow_delimiter(|b| b == b' ')
    ///     .build();
    ///
    /// assert_eq!(parser.parse("1 ns").unwrap(), Duration::new(0, 1));
    /// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
    ///
    /// // instead of
    ///
    /// let mut parser = DurationParser::with_all_time_units();
    /// parser
    ///     .default_unit(MicroSecond)
    ///     .allow_delimiter(Some(|b| b == b' '));
    ///
    /// assert_eq!(parser.parse("1 ns").unwrap(), Duration::new(0, 1));
    /// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
    /// ```
    pub const fn builder() -> CustomDurationParserBuilder<'a> {
        CustomDurationParserBuilder::new()
    }

    /// Add a custom time unit to the current set of [`TimeUnit`]s.
    ///
    /// Custom time units have a base [`TimeUnit`] and a [`Multiplier`] in addition to their
    /// identifiers.
    ///
    /// # Panics
    ///
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, CustomTimeUnit, Multiplier};
    ///
    /// let mut parser = CustomDurationParser::new();
    /// parser
    ///     .custom_time_unit(CustomTimeUnit::new(
    ///         Week,
    ///         &["fortnight", "fortnights"],
    ///         Some(Multiplier(2, 0)),
    ///     ))
    ///     .custom_time_unit(CustomTimeUnit::new(
    ///         Second,
    ///         &["kilosecond", "kiloseconds", "kilos"],
    ///         Some(Multiplier(1000, 0)),
    ///     ))
    ///     .custom_time_unit(CustomTimeUnit::new(
    ///         Second,
    ///         &["shakes"],
    ///         Some(Multiplier(1, -8)),
    ///     ));
    /// assert_eq!(
    ///     parser.parse("1fortnights").unwrap(),
    ///     Duration::new(2 * 7 * 24 * 60 * 60, 0),
    /// );
    /// ```
    ///
    /// The `base_unit` is only used to calculate the final duration and does not need to be
    /// unique in the set of time units. It's even possible to define an own time unit for
    /// example for a definition of a [`TimeUnit::Year`] either in addition or as a
    /// replacement of the year definition of this crate (Julian Year = `365.25` days).
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, CustomTimeUnit, Multiplier, DEFAULT_TIME_UNITS};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
    /// // The common year is usually defined as 365 days
    /// parser.custom_time_unit(CustomTimeUnit::new(
    ///     Day,
    ///     &["y", "year", "years"],
    ///     Some(Multiplier(356, 0)),
    /// ));
    /// assert_eq!(
    ///     parser.parse("1year").unwrap(),
    ///     Duration::new(356 * 24 * 60 * 60, 0),
    /// );
    /// ```
    pub fn custom_time_unit(&mut self, time_unit: CustomTimeUnit<'a>) -> &mut Self {
        self.time_units.add_custom_time_unit(time_unit);
        self
    }

    /// Add multiple [`CustomTimeUnit`]s at once.
    ///
    /// See also [`CustomDurationParser::custom_time_unit`]
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, CustomTimeUnit, Multiplier};
    ///
    /// const CUSTOM_TIME_UNITS: [CustomTimeUnit; 2] = [
    ///     CustomTimeUnit::new(Week, &["fortnight", "fortnights"], Some(Multiplier(2, 0))),
    ///     CustomTimeUnit::new(Second, &["shake", "shakes"], Some(Multiplier(1, -8))),
    /// ];
    ///
    /// let mut parser = CustomDurationParser::new();
    /// parser.custom_time_units(&CUSTOM_TIME_UNITS);
    ///
    /// assert_eq!(
    ///     parser.parse("1fortnight").unwrap(),
    ///     Duration::new(2 * 7 * 24 * 60 * 60, 0),
    /// );
    /// ```
    pub fn custom_time_units(&mut self, time_units: &[CustomTimeUnit<'a>]) -> &mut Self {
        for time_unit in time_units {
            self.custom_time_unit(*time_unit);
        }
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
    /// use std::time::Duration;
    ///
    /// use fundu::CustomDurationParser;
    ///
    /// assert_eq!(
    ///     CustomDurationParser::new().parse("1.2e-1").unwrap(),
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
    /// use fundu::CustomDurationParser;
    ///
    /// assert_eq!(
    ///     CustomDurationParser::new()
    ///         .parse_negative("-10.2e-1")
    ///         .unwrap(),
    ///     time::Duration::new(-1, -20_000_000),
    /// );
    /// assert_eq!(
    ///     CustomDurationParser::new()
    ///         .parse_negative("1.2e-1")
    ///         .unwrap(),
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
    /// use fundu::CustomDurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     CustomDurationParser::new()
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
    /// See also [`crate::DurationParser::allow_delimiter`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, ParseError};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&[(NanoSecond, &["ns"])]);
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
    /// assert_eq!(parser.parse("123\t\n\r ns"), Ok(Duration::new(0, 123)));
    /// ```
    pub fn allow_delimiter(&mut self, delimiter: Option<Delimiter>) -> &mut Self {
        self.inner.config.allow_delimiter = delimiter;
        self
    }

    /// Disable parsing the exponent.
    ///
    /// See also [`crate::DurationParser::disable_exponent`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParser, ParseError, DEFAULT_TIME_UNITS};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
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

    /// Disable parsing a fraction in the source string.
    ///
    /// See also [`crate::DurationParser::disable_fraction`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, ParseError};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&[(NanoSecond, &["ns"])]);
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
    /// See also [`crate::DurationParser::disable_infinity`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParser, ParseError};
    ///
    /// let mut parser = CustomDurationParser::new();
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

    /// This setting makes a number in the source string optional.
    ///
    /// See also [`crate::DurationParser::number_is_optional`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::{CustomDurationParser, DEFAULT_TIME_UNITS};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
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
    /// See also [`crate::DurationParser::parse_multiple`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::{CustomDurationParser, DEFAULT_TIME_UNITS};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
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

    /// Try to find the [`TimeUnit`] with it's associate [`Multiplier`] by id
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, Multiplier};
    ///
    /// let parser =
    ///     CustomDurationParser::with_time_units(&[(NanoSecond, &["ns"]), (MicroSecond, &["Ms"])]);
    ///
    /// assert_eq!(parser.get_time_unit_by_id("does_not_exist"), None);
    ///
    /// for (time_unit, id) in &[(NanoSecond, "ns"), (MicroSecond, "Ms")] {
    ///     assert_eq!(
    ///         parser.get_time_unit_by_id(id),
    ///         Some((*time_unit, Multiplier(1, 0)))
    ///     );
    /// }
    /// ```
    pub fn get_time_unit_by_id(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        self.time_units.get(identifier)
    }

    /// Return true if there are haven't been any time units added, yet.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::CustomDurationParser;
    ///
    /// let parser = CustomDurationParser::new();
    /// assert!(parser.is_empty())
    /// ```
    pub fn is_empty(&self) -> bool {
        self.time_units.is_empty()
    }
}

impl<'a> Default for CustomDurationParser<'a> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;
    use crate::custom::builder::CustomDurationParserBuilder;
    use crate::custom::time_units::DEFAULT_ALL_TIME_UNITS;
    use crate::TimeUnit::*;

    const YEAR: u64 = 60 * 60 * 24 * 365 + 60 * 60 * 24 / 4;
    const MONTH: u64 = YEAR / 12;

    #[test]
    fn test_custom_duration_parser_init_new() {
        let parser = CustomDurationParser::new();
        assert_eq!(parser.inner.config.default_unit, Second);
        assert!(parser.time_units.is_empty());
        assert_eq!(parser.parse("1.0"), Ok(Duration::new(1, 0)));
        assert_eq!(
            parser.parse("1.0s"),
            Err(ParseError::TimeUnit(
                3,
                "No time units allowed but found: 's'".to_string()
            ))
        );
    }

    #[test]
    fn test_custom_duration_parser_init_with_time_units() {
        let parser = CustomDurationParser::with_time_units(&DEFAULT_ALL_TIME_UNITS);
        assert_eq!(parser.inner.config.default_unit, Second);
        for (time_unit, ids) in DEFAULT_ALL_TIME_UNITS {
            for id in ids {
                assert_eq!(
                    parser.get_time_unit_by_id(id),
                    Some((time_unit, Multiplier::default()))
                );
            }
        }
        assert_eq!(parser.parse("1.0"), Ok(Duration::new(1, 0)));
    }

    #[test]
    fn test_custom_duration_parser_init_default() {
        let parser = CustomDurationParser::default();
        assert!(parser.time_units.is_empty());
    }

    #[test]
    fn test_custom_duration_parser_when_add_custom_time_units() {
        let ids = ["century", "centuries"];
        let mut parser = CustomDurationParser::new();
        parser.custom_time_unit(CustomTimeUnit::new(Year, &ids, Some(Multiplier(100, 0))));
        for id in ids {
            assert_eq!(
                parser.get_time_unit_by_id(id),
                Some((Year, Multiplier(100, 0)))
            );
        }
    }

    #[test]
    fn test_custom_duration_parser_when_setting_default_time_unit() {
        let mut parser = CustomDurationParser::new();
        parser.default_unit(NanoSecond);

        assert_eq!(parser.inner.config.default_unit, NanoSecond);
        assert_eq!(parser.parse("1"), Ok(Duration::new(0, 1)));
    }

    #[rstest]
    #[case::nano_second("1ns", Duration::new(0, 1))]
    #[case::micro_second("1Ms", Duration::new(0, 1000))]
    #[case::milli_second("1ms", Duration::new(0, 1_000_000))]
    #[case::second("1s", Duration::new(1, 0))]
    #[case::minute("1m", Duration::new(60, 0))]
    #[case::hour("1h", Duration::new(60 * 60, 0))]
    #[case::day("1d", Duration::new(60 * 60 * 24, 0))]
    #[case::week("1w", Duration::new(60 * 60 * 24 * 7, 0))]
    #[case::month("1M", Duration::new(MONTH, 0))]
    #[case::year("1y", Duration::new(YEAR, 0))]
    fn test_custom_duration_parser_parse_when_default_time_units(
        #[case] input: &str,
        #[case] expected: Duration,
    ) {
        let parser = CustomDurationParser::with_time_units(&DEFAULT_ALL_TIME_UNITS);
        assert_eq!(parser.parse(input), Ok(expected));
    }

    #[test]
    fn test_custom_duration_parser_parse_when_non_ascii() {
        let parser = CustomDurationParser::with_time_units(&[(MilliSecond, &["мілісекунда"])]);
        assert_eq!(
            parser.parse("1мілісекунда"),
            Ok(Duration::new(0, 1_000_000))
        );
    }

    #[test]
    fn test_custom_duration_parser_setting_allow_spaces() {
        let mut parser = CustomDurationParser::new();
        parser.allow_delimiter(Some(|b| b == b' '));
        assert!(parser.inner.config.allow_delimiter.unwrap()(b' '));
    }

    #[test]
    fn test_custom_duration_parser_setting_disable_fraction() {
        let mut parser = CustomDurationParser::new();
        parser.disable_fraction(true);
        assert!(parser.inner.config.disable_fraction);
    }

    #[test]
    fn test_custom_duration_parser_setting_disable_exponent() {
        let mut parser = CustomDurationParser::new();
        parser.disable_exponent(true);
        assert!(parser.inner.config.disable_exponent);
    }

    #[test]
    fn test_custom_duration_parser_setting_disable_infinity() {
        let mut parser = CustomDurationParser::new();
        parser.disable_infinity(true);
        assert!(parser.inner.config.disable_infinity);
    }

    #[test]
    fn test_custom_duration_parser_setting_number_is_optional() {
        let mut parser = CustomDurationParser::new();
        parser.number_is_optional(true);
        assert!(parser.inner.config.number_is_optional);
    }

    #[test]
    fn test_custom_duration_parser_setting_parse_multiple() {
        let mut parser = CustomDurationParser::new();
        parser.parse_multiple(Some(|byte| byte == 0xff));

        assert!(parser.inner.config.multiple.unwrap()(0xff));
    }

    #[cfg(feature = "negative")]
    #[test]
    fn test_custom_duration_parser_parse_negative_calls_parser() {
        use crate::config::Config;

        let parser = CustomDurationParser::new();
        assert_eq!(parser.inner.config, Config::new());
        assert_eq!(
            parser.parse_negative("1s"),
            Err(ParseError::TimeUnit(
                1,
                "No time units allowed but found: 's'".to_string()
            ))
        );
        assert_eq!(
            parser.parse_negative("-1.0e0"),
            Ok(time::Duration::new(-1, 0))
        )
    }

    #[test]
    fn test_custom_duration_parser_method_builder() {
        assert_eq!(
            CustomDurationParser::builder(),
            CustomDurationParserBuilder::new()
        );
    }

    #[test]
    fn test_custom_duration_parser_when_adding_custom_time_units() {
        let time_units = [
            CustomTimeUnit::new(Second, &["sec"], Some(Multiplier(1, 0))),
            CustomTimeUnit::new(Second, &["secs"], Some(Multiplier(2, 0))),
        ];
        let mut custom = CustomDurationParser::new();
        custom.custom_time_units(&time_units);
        assert_eq!(
            custom.get_time_unit_by_id("sec"),
            Some((Second, Multiplier(1, 0)))
        );
        assert_eq!(
            custom.get_time_unit_by_id("secs"),
            Some((Second, Multiplier(2, 0)))
        );
    }

    #[test]
    fn test_custom_duration_parser_when_calling_custom_time_units_with_empty_collection() {
        let mut custom = CustomDurationParser::new();
        assert!(custom.is_empty());

        custom.custom_time_units(&[]);
        assert!(custom.is_empty());
    }
}
