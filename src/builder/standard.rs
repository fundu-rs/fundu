// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

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
        self.data.iter().all(|b| b.is_none())
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
/// See also the [module level documentation](crate) for more details and more information about the
/// format.
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
    /// use fundu::TimeUnit::*;
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
    /// use std::time::Duration;
    ///
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
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse("1.2e-1s").unwrap(),
    ///     Duration::new(0, 120_000_000),
    /// );
    /// ```
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
    /// use fundu::TimeUnit::*;
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
    pub fn parse_negative(&self, source: &str) -> Result<time::Duration, ParseError> {
        self.inner.parse_negative(source, &self.time_units)
    }

    /// Add a time unit to the current set of [`TimeUnit`]s.
    ///
    /// Adding an already existing [`TimeUnit`] has no effect.
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
    ///     DurationParser::new()
    ///         .time_unit(Month)
    ///         .time_unit(Year)
    ///         .get_current_time_units(),
    ///     DurationParser::with_all_time_units().get_current_time_units(),
    /// );
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units()
    ///         .time_unit(Second)
    ///         .get_current_time_units(),
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
    /// use std::time::Duration;
    ///
    /// use fundu::DurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     DurationParser::without_time_units()
    ///         .time_units(&[MicroSecond, MilliSecond])
    ///         .get_current_time_units(),
    ///     vec![MicroSecond, MilliSecond],
    /// );
    /// ```
    pub fn time_units(&mut self, units: &[TimeUnit]) -> &mut Self {
        self.time_units.add_time_units(units);
        self
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
    pub fn default_unit(&mut self, unit: TimeUnit) -> &Self {
        self.inner.config.default_unit = unit;
        self
    }

    /// Allow spaces between the number and the [`TimeUnit`].
    ///
    /// Per default no spaces are allowed between the number and the [`TimeUnit`]. This setting
    /// implicitly allows spaces at the end of the string if no time unit was present.
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
    ///     Err(ParseError::Syntax(3, "No spaces allowed".to_string()))
    /// );
    ///
    /// parser.allow_spaces();
    /// assert_eq!(parser.parse("123 ns"), Ok(Duration::new(0, 123)));
    /// assert_eq!(parser.parse("123 "), Ok(Duration::new(123, 0)));
    /// ```
    pub fn allow_spaces(&mut self) -> &mut Self {
        self.inner.config.allow_spaces = true;
        self
    }

    /// Disable parsing an exponent.
    ///
    /// If an exponent is encountered in the input string and this setting is active this results in
    /// an [`ParseError::Syntax`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{DurationParser, ParseError};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.disable_exponent();
    /// assert_eq!(
    ///     parser.parse("123e+1"),
    ///     Err(ParseError::Syntax(3, "No exponent allowed".to_string()))
    /// );
    /// ```
    pub fn disable_exponent(&mut self) -> &mut Self {
        self.inner.config.disable_exponent = true;
        self
    }

    /// Disable parsing a fraction in the source string.
    ///
    /// This setting will disable parsing a fraction and a point delimiter will cause an error
    /// [`ParseError::Syntax`]. This does not prevent [`Duration`]s from being smaller than seconds.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{DurationParser, ParseError};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.disable_fraction();
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
    pub fn disable_fraction(&mut self) -> &mut Self {
        self.inner.config.disable_fraction = true;
        self
    }

    /// This setting makes a number in the source string optional.
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
    /// use fundu::TimeUnit::*;
    /// use fundu::{DurationParser, ParseError};
    ///
    /// let mut parser = DurationParser::new();
    /// parser.number_is_optional();
    ///
    /// for input in &["ns", "e-9", "e-3Ms"] {
    ///     assert_eq!(parser.parse(input), Ok(Duration::new(0, 1)));
    /// }
    /// ```
    pub fn number_is_optional(&mut self) -> &mut Self {
        self.inner.config.number_is_optional = true;
        self
    }

    /// Return the currently defined set of [`TimeUnit`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// let mut parser = DurationParser::without_time_units();
    /// assert_eq!(
    ///     parser.get_current_time_units(),
    ///     vec![]
    /// );
    ///
    /// assert_eq!(
    ///     parser.time_unit(NanoSecond).get_current_time_units(),
    ///     vec![NanoSecond]
    /// );
    pub fn get_current_time_units(&self) -> Vec<TimeUnit> {
        self.time_units.get_time_units()
    }
}

impl Default for DurationParser {
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
/// See also the [module level documentation](crate) for more details and more information about the
/// format.
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
///     Err(ParseError::Syntax(0, "Invalid character: 'N'".to_string()))
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
    fn test_duration_parser_setting_allow_spaces() {
        let mut parser = DurationParser::new();
        parser.allow_spaces();
        assert!(parser.inner.config.allow_spaces);
    }
}
