// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use crate::parse::ReprParser;
use crate::time::TimeUnitsLike;
use crate::{
    ParseError, TimeUnit, TimeUnit::*, DEFAULT_ID_DAY, DEFAULT_ID_HOUR, DEFAULT_ID_MICRO_SECOND,
    DEFAULT_ID_MILLI_SECOND, DEFAULT_ID_MINUTE, DEFAULT_ID_MONTH, DEFAULT_ID_NANO_SECOND,
    DEFAULT_ID_SECOND, DEFAULT_ID_WEEK, DEFAULT_ID_YEAR,
};

/// Interface for [`TimeUnit`]s providing common methods to manipulate the available time units.
#[derive(Debug, PartialEq)]
pub struct TimeUnits {
    nanos: Option<&'static str>,
    micros: Option<&'static str>,
    millis: Option<&'static str>,
    seconds: Option<&'static str>,
    minutes: Option<&'static str>,
    hours: Option<&'static str>,
    days: Option<&'static str>,
    weeks: Option<&'static str>,
    months: Option<&'static str>,
    years: Option<&'static str>,
}

impl Default for TimeUnits {
    fn default() -> Self {
        Self {
            nanos: Some(DEFAULT_ID_NANO_SECOND),
            micros: Some(DEFAULT_ID_MICRO_SECOND),
            millis: Some(DEFAULT_ID_MILLI_SECOND),
            seconds: Some(DEFAULT_ID_SECOND),
            minutes: Some(DEFAULT_ID_MINUTE),
            hours: Some(DEFAULT_ID_HOUR),
            days: Some(DEFAULT_ID_DAY),
            weeks: Some(DEFAULT_ID_WEEK),
            months: Default::default(),
            years: Default::default(),
        }
    }
}

impl TimeUnitsLike for TimeUnits {
    /// Return `true` if this set of time units is empty.
    fn is_empty(&self) -> bool {
        self.nanos.is_none()
            && self.micros.is_none()
            && self.millis.is_none()
            && self.seconds.is_none()
            && self.minutes.is_none()
            && self.hours.is_none()
            && self.days.is_none()
            && self.weeks.is_none()
            && self.months.is_none()
            && self.years.is_none()
    }

    /// Return the [`TimeUnit`] associated with the provided `identifier`.
    ///
    /// Returns `None` if no [`TimeUnit`] with the provided `identifier` is present in the current
    /// set of time units.
    fn get(&self, identifier: &str) -> Option<TimeUnit> {
        match identifier.len() {
            1 => {
                let id = Some(identifier);
                if id == self.seconds {
                    Some(Second)
                } else if id == self.minutes {
                    Some(Minute)
                } else if id == self.hours {
                    Some(Hour)
                } else if id == self.days {
                    Some(Day)
                } else if id == self.weeks {
                    Some(Week)
                } else if id == self.months {
                    Some(Month)
                } else if id == self.years {
                    Some(Year)
                } else {
                    None
                }
            }
            2 => {
                let id = Some(identifier);
                if id == self.nanos {
                    Some(NanoSecond)
                } else if id == self.micros {
                    Some(MicroSecond)
                } else if id == self.millis {
                    Some(MilliSecond)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

impl TimeUnits {
    /// Create an empty set of [`TimeUnit`]s.
    fn new() -> Self {
        Self {
            nanos: Default::default(),
            micros: Default::default(),
            millis: Default::default(),
            seconds: Default::default(),
            minutes: Default::default(),
            hours: Default::default(),
            days: Default::default(),
            weeks: Default::default(),
            months: Default::default(),
            years: Default::default(),
        }
    }

    /// Create [`TimeUnits`] with a custom set of [`TimeUnit`]s.
    fn with_time_units(units: &[TimeUnit]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

    /// Create [`TimeUnits`] with default [`TimeUnit`]s.
    fn with_default_time_units() -> Self {
        Self::default()
    }

    /// Create [`TimeUnits`] with a all available [`TimeUnit`]s.
    fn with_all_time_units() -> Self {
        Self {
            nanos: Some(DEFAULT_ID_NANO_SECOND),
            micros: Some(DEFAULT_ID_MICRO_SECOND),
            millis: Some(DEFAULT_ID_MILLI_SECOND),
            seconds: Some(DEFAULT_ID_SECOND),
            minutes: Some(DEFAULT_ID_MINUTE),
            hours: Some(DEFAULT_ID_HOUR),
            days: Some(DEFAULT_ID_DAY),
            weeks: Some(DEFAULT_ID_WEEK),
            months: Some(DEFAULT_ID_MONTH),
            years: Some(DEFAULT_ID_YEAR),
        }
    }

    /// Add a [`TimeUnit`] to the set of already present time units.
    fn add_time_unit(&mut self, unit: TimeUnit) {
        match unit {
            NanoSecond => {
                self.nanos = Some(DEFAULT_ID_NANO_SECOND);
            }
            MicroSecond => {
                self.micros = Some(DEFAULT_ID_MICRO_SECOND);
            }
            MilliSecond => {
                self.millis = Some(DEFAULT_ID_MILLI_SECOND);
            }
            Second => {
                self.seconds = Some(DEFAULT_ID_SECOND);
            }
            Minute => {
                self.minutes = Some(DEFAULT_ID_MINUTE);
            }
            Hour => {
                self.hours = Some(DEFAULT_ID_HOUR);
            }
            Day => {
                self.days = Some(DEFAULT_ID_DAY);
            }
            Week => {
                self.weeks = Some(DEFAULT_ID_WEEK);
            }
            Month => {
                self.months = Some(DEFAULT_ID_MONTH);
            }
            Year => {
                self.years = Some(DEFAULT_ID_YEAR);
            }
        };
    }

    /// Add multiple [`TimeUnit`] to the set of already present time units.
    fn add_time_units(&mut self, units: &[TimeUnit]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    /// Return all [`TimeUnit`]s from the set of active time units ordered.
    fn get_time_units(&self) -> Vec<TimeUnit> {
        let mut time_units = Vec::with_capacity(10);
        for (unit, value) in &[
            (NanoSecond, self.nanos),
            (MicroSecond, self.micros),
            (MilliSecond, self.millis),
            (Second, self.seconds),
            (Minute, self.minutes),
            (Hour, self.hours),
            (Day, self.days),
            (Week, self.weeks),
            (Month, self.months),
            (Year, self.years),
        ] {
            if value.is_some() {
                time_units.push(*unit);
            }
        }
        time_units
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
    pub fn parse(&self, source: &str) -> Result<Duration, ParseError> {
        let mut parser = ReprParser::new(source, self.default_unit, &self.time_units);
        parser.parse().and_then(|mut repr| repr.parse())
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

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    fn assert_time_unit(time_units: &TimeUnits, time_unit: TimeUnit, expected: Option<&str>) {
        let id = match time_unit {
            NanoSecond => time_units.nanos,
            MicroSecond => time_units.micros,
            MilliSecond => time_units.millis,
            Second => time_units.seconds,
            Minute => time_units.minutes,
            Hour => time_units.hours,
            Day => time_units.days,
            Week => time_units.weeks,
            Month => time_units.months,
            Year => time_units.years,
        };
        assert_eq!(id, expected);
    }

    #[allow(clippy::too_many_arguments)]
    fn assert_time_units<'a>(
        time_units: &TimeUnits,
        nanos: Option<&'a str>,
        micros: Option<&'a str>,
        millis: Option<&'a str>,
        seconds: Option<&'a str>,
        minutes: Option<&'a str>,
        hours: Option<&'a str>,
        days: Option<&'a str>,
        weeks: Option<&'a str>,
        months: Option<&'a str>,
        years: Option<&'a str>,
    ) {
        assert_eq!(time_units.nanos, nanos);
        assert_eq!(time_units.micros, micros);
        assert_eq!(time_units.millis, millis);
        assert_eq!(time_units.seconds, seconds);
        assert_eq!(time_units.minutes, minutes);
        assert_eq!(time_units.hours, hours);
        assert_eq!(time_units.days, days);
        assert_eq!(time_units.weeks, weeks);
        assert_eq!(time_units.months, months);
        assert_eq!(time_units.years, years);
    }

    #[test]
    fn test_time_units_new() {
        let time_units = TimeUnits::new();
        assert_time_units(
            &time_units,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
        );
    }

    #[test]
    fn test_time_units_with_default_time_units() {
        let time_units = TimeUnits::with_default_time_units();
        assert_eq!(time_units, TimeUnits::default());

        assert_time_units(
            &time_units,
            Some("ns"),
            Some("Ms"),
            Some("ms"),
            Some("s"),
            Some("m"),
            Some("h"),
            Some("d"),
            Some("w"),
            None,
            None,
        );
    }

    #[test]
    fn test_time_units_with_all_time_units() {
        let time_units = TimeUnits::with_all_time_units();
        assert_time_units(
            &time_units,
            Some("ns"),
            Some("Ms"),
            Some("ms"),
            Some("s"),
            Some("m"),
            Some("h"),
            Some("d"),
            Some("w"),
            Some("M"),
            Some("y"),
        );
    }

    #[test]
    fn test_time_units_with_time_units() {
        let time_units = TimeUnits::with_time_units(&[NanoSecond]);
        assert_time_units(
            &time_units,
            Some("ns"),
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
        );
    }

    #[rstest]
    #[case::nano_second(NanoSecond, Some("ns"))]
    #[case::nano_second(MicroSecond, Some("Ms"))]
    #[case::nano_second(MilliSecond, Some("ms"))]
    #[case::nano_second(Second, Some("s"))]
    #[case::nano_second(Minute, Some("m"))]
    #[case::nano_second(Hour, Some("h"))]
    #[case::nano_second(Day, Some("d"))]
    #[case::nano_second(Week, Some("w"))]
    #[case::nano_second(Month, Some("M"))]
    #[case::nano_second(Year, Some("y"))]
    fn test_time_units_add_time_unit(#[case] time_unit: TimeUnit, #[case] expected: Option<&str>) {
        let mut time_units = TimeUnits::new();
        time_units.add_time_unit(time_unit);
        assert_time_unit(&time_units, time_unit, expected);
        assert_eq!(time_units.get_time_units(), vec![time_unit]);
    }

    #[test]
    fn test_time_units_add_time_unit_twice() {
        let mut time_units = TimeUnits::new();
        let time_unit = MicroSecond;

        time_units.add_time_unit(time_unit);
        time_units.add_time_unit(time_unit);

        assert!(time_units.micros.is_some());
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
    #[case::nano_second("ns", Some(NanoSecond))]
    #[case::micro_second("Ms", Some(MicroSecond))]
    #[case::milli_second("ms", Some(MilliSecond))]
    #[case::second("s", Some(Second))]
    #[case::minute("m", Some(Minute))]
    #[case::hour("h", Some(Hour))]
    #[case::day("d", Some(Day))]
    #[case::week("w", Some(Week))]
    #[case::month("M", Some(Month))]
    #[case::year("y", Some(Year))]
    fn test_time_units_get(#[case] id: &str, #[case] expected: Option<TimeUnit>) {
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
        let parser = DurationParser::default();
        assert!(!parser.time_units.is_empty());
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
}
