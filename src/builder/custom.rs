// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use crate::parse::ReprParser;
use crate::time::TimeUnitsLike;
use crate::{
    ParseError, TimeUnit, TimeUnit::*, DEFAULT_ID_DAY, DEFAULT_ID_HOUR, DEFAULT_ID_MICRO_SECOND,
    DEFAULT_ID_MILLI_SECOND, DEFAULT_ID_MINUTE, DEFAULT_ID_MONTH, DEFAULT_ID_NANO_SECOND,
    DEFAULT_ID_SECOND, DEFAULT_ID_WEEK, DEFAULT_ID_YEAR,
};
use std::time::Duration;

/// Part of the `custom` feature with [`TimeUnit`] ids as defined in [`systemd.time`](https://www.man7.org/linux/man-pages/man7/systemd.time.7.html)
pub const SYSTEMD_TIME_UNITS: [(TimeUnit, &[&str]); 10] = [
    (NanoSecond, &["ns", "nsec"]),
    (MicroSecond, &["us", "µs", "usec"]),
    (MilliSecond, &["ms", "msec"]),
    (Second, &["s", "sec", "second", "seconds"]),
    (Minute, &["m", "min", "minute", "minutes"]),
    (Hour, &["h", "hr", "hour", "hours"]),
    (Day, &["d", "day", "days"]),
    (Week, &["w", "week", "weeks"]),
    (Month, &["M", "month", "months"]),
    (Year, &["y", "year", "years"]),
];

/// Part of the `custom` feature with all [`TimeUnit`] ids as defined in the `default` feature
pub const DEFAULT_TIME_UNITS: [(TimeUnit, &[&str]); 10] = [
    (NanoSecond, &[DEFAULT_ID_NANO_SECOND]),
    (MicroSecond, &[DEFAULT_ID_MICRO_SECOND]),
    (MilliSecond, &[DEFAULT_ID_MILLI_SECOND]),
    (Second, &[DEFAULT_ID_SECOND]),
    (Minute, &[DEFAULT_ID_MINUTE]),
    (Hour, &[DEFAULT_ID_HOUR]),
    (Day, &[DEFAULT_ID_DAY]),
    (Week, &[DEFAULT_ID_WEEK]),
    (Month, &[DEFAULT_ID_MONTH]),
    (Year, &[DEFAULT_ID_YEAR]),
];

type Identifiers<'a> = (TimeUnit, Vec<&'a str>);
type IdentifiersSlice<'a> = (TimeUnit, &'a [&'a str]);

#[derive(Debug)]
struct CustomTimeUnits<'a> {
    time_units: [Identifiers<'a>; 10],
}

impl<'a> CustomTimeUnits<'a> {
    fn map_time_unit_to_index(unit: TimeUnit) -> usize {
        match unit {
            NanoSecond => 0,
            MicroSecond => 1,
            MilliSecond => 2,
            Second => 3,
            Minute => 4,
            Hour => 5,
            Day => 6,
            Week => 7,
            Month => 8,
            Year => 9,
        }
    }
}

impl<'a> TimeUnitsLike<IdentifiersSlice<'a>> for CustomTimeUnits<'a> {
    fn new() -> Self {
        let capacity = 5;
        Self {
            time_units: [
                (NanoSecond, Vec::with_capacity(capacity)),
                (MicroSecond, Vec::with_capacity(capacity)),
                (MilliSecond, Vec::with_capacity(capacity)),
                (Second, Vec::with_capacity(capacity)),
                (Minute, Vec::with_capacity(capacity)),
                (Hour, Vec::with_capacity(capacity)),
                (Day, Vec::with_capacity(capacity)),
                (Week, Vec::with_capacity(capacity)),
                (Month, Vec::with_capacity(capacity)),
                (Year, Vec::with_capacity(capacity)),
            ],
        }
    }

    fn with_time_units(units: &[IdentifiersSlice<'a>]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

    fn add_time_unit(&mut self, unit: IdentifiersSlice<'a>) {
        let (time_unit, ids) = unit;
        self.time_units[Self::map_time_unit_to_index(time_unit)]
            .1
            .extend(ids.iter().filter(|s| !s.is_empty()))
    }

    fn add_time_units(&mut self, units: &[IdentifiersSlice<'a>]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    fn is_empty(&self) -> bool {
        self.time_units.iter().all(|(_, v)| v.is_empty())
    }

    fn get(&self, identifier: &str) -> Option<TimeUnit> {
        // TODO: improve performance with pre-filtering by first character of `identifier`
        for (t, v) in self.time_units.iter() {
            if v.contains(&identifier) {
                return Some(*t);
            }
        }
        None
    }

    fn get_time_units(&self) -> Vec<TimeUnit> {
        self.time_units
            .iter()
            .filter_map(|(t, v)| if !v.is_empty() { Some(*t) } else { None })
            .collect()
    }
}

/// A parser with a customizable set of [`TimeUnit`]s and customizable identifiers.
pub struct CustomDurationParser<'a> {
    time_units: CustomTimeUnits<'a>,
    default_unit: TimeUnit,
}

impl<'a> CustomDurationParser<'a> {
    /// Create a new empty [`CustomDurationParser`].
    ///
    /// Add time units as you like with [`CustomDurationParser::time_unit`] or multiple time units
    /// at once with [`CustomDurationParser::time_units`]. Note there's also
    /// [`CustomDurationParser::with_time_units`] which initializes the parser with a set time units with
    /// custom `ids`. The default time unit can be changed with
    /// [`CustomDurationParser::default_unit`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// let mut parser = CustomDurationParser::new();
    /// assert_eq!(
    ///     parser.get_current_time_units(),
    ///     vec![]
    /// );
    ///
    /// assert_eq!(
    ///     parser.parse("100.0").unwrap(),
    ///     Duration::new(100, 0)
    /// );
    ///
    /// parser.default_unit(Minute);
    /// assert_eq!(
    ///     parser.parse("1.0e2").unwrap(),
    ///     Duration::new(6000, 0)
    /// );
    /// ```
    pub fn new() -> Self {
        Self {
            time_units: CustomTimeUnits::new(),
            default_unit: Default::default(),
        }
    }

    /// Create a new [`CustomDurationParser`] with an initial set of custom identifiers for each
    /// [`TimeUnit`]s in `units`.
    ///
    /// Not all time units need to be defined, so if there is no intention to include a specific
    /// [`TimeUnit`] just leave it out of the `units`. Be aware, that this library does not check
    /// the validity of identifiers, so besides the need to be a valid `utf-8` sequence there are no
    /// other limitations. There is also no check for duplicate `ids`, and empty `ids` are ignored.
    /// Note the ids for time units are case sensitive.
    ///
    /// You may find it helpful to start with a pre-defined custom sets of [`TimeUnit`]:
    /// * [`SYSTEMD_TIME_UNITS`]: This is the set of time units as specified in the
    ///   [`systemd.time`](https://www.man7.org/linux/man-pages/man7/systemd.time.7.html)
    ///   documentation
    /// * [`DEFAULT_TIME_UNITS`]: This is the complete set of time units with their default ids as
    ///   used the standard crate by [`crate::DurationParser`]
    ///
    /// # Security
    ///
    /// If there is the intention to expose the defining of [`TimeUnit`]s to an untrusted source,
    /// you may be good advised to limit the possible characters to something safer like
    /// [`char::is_alphabetic`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// let mut parser = CustomDurationParser::with_time_units(
    ///     &[(Second, &["s"]), (Minute, &["Min"]), (Hour, &["ώρα"])]
    /// );
    /// assert_eq!(
    ///     parser.get_current_time_units(),
    ///     vec![Second, Minute, Hour]
    /// );
    ///
    /// assert!(parser.parse("42.0min").is_err()); // Note the small letter `m` instead of `M`
    ///
    /// assert_eq!(
    ///     parser.parse("42e-1ώρα").unwrap(),
    ///     Duration::new(15120, 0)
    /// );
    /// ```
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
    /// use fundu::{CustomDurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     CustomDurationParser::new().default_unit(NanoSecond).parse("42").unwrap(),
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
    /// use fundu::{CustomDurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// let mut parser = CustomDurationParser::new();
    /// assert_eq!(
    ///     parser.get_current_time_units(),
    ///     vec![]
    /// );
    ///
    /// assert_eq!(
    ///     parser.time_unit(NanoSecond, &["ns"]).get_current_time_units(),
    ///     vec![NanoSecond]
    /// );
    pub fn get_current_time_units(&self) -> Vec<TimeUnit> {
        self.time_units.get_time_units()
    }

    /// Add a custom [`TimeUnit`] with the specified `identifier`s to the current set of time units.
    ///
    /// This method can be called multiple times for the same [`TimeUnit`] and just appends the
    /// `ids` to the existing set.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// let mut parser = CustomDurationParser::new();;
    /// parser.time_unit(Minute, &["minutes", "λεπτό"]);
    ///
    /// assert_eq!(
    ///     parser.parse("42minutes").unwrap(),
    ///     Duration::new(2520, 0)
    /// );
    ///
    /// assert_eq!(
    ///     parser.parse("42λεπτό").unwrap(),
    ///     Duration::new(2520, 0)
    /// );
    ///
    /// assert!(parser.parse("42Minutes").is_err());
    ///
    /// parser.time_unit(Minute, &["Minutes"]);
    ///
    /// assert_eq!(
    ///     parser.parse("42Minutes").unwrap(),
    ///     Duration::new(2520, 0)
    /// );
    /// ```
    pub fn time_unit(&mut self, unit: TimeUnit, identifiers: &'a [&'a str]) -> &mut Self {
        self.time_units.add_time_unit((unit, identifiers));
        self
    }

    /// Add multiple [`TimeUnit`]s to the current set of time units.
    ///
    /// This method calls [`CustomDurationParser::time_unit`] for every [`TimeUnit`] found in
    /// `units`. See [`CustomDurationParser::with_time_units`] for thorough documentation of valid
    /// `identifiers`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::{CustomDurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// let mut parser = CustomDurationParser::new();
    /// assert_eq!(
    ///     parser.time_units(
    ///         &[(MicroSecond, &["µ", "Ms"]), (Second, &["s", "seconds"])]
    ///     )
    ///     .parse("1µ")
    ///     .unwrap(),
    ///     Duration::new(0, 1000),
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
    /// use fundu::{CustomDurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     CustomDurationParser::new().parse("1.2e-1").unwrap(),
    ///     Duration::new(0, 120_000_000),
    /// );
    /// ```
    #[inline(never)]
    pub fn parse(&self, source: &str) -> Result<Duration, ParseError> {
        let mut parser = ReprParser::new(source, self.default_unit, &self.time_units);
        parser.parse().and_then(|mut repr| repr.parse())
    }
}

impl<'a> Default for CustomDurationParser<'a> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    const YEAR: u64 = 60 * 60 * 24 * 365 + 60 * 60 * 24 / 4; // 365 days + day/4
    const MONTH: u64 = YEAR / 12;

    #[test]
    fn test_custom_time_units_init_new() {
        let custom = CustomTimeUnits::new();
        assert_eq!(custom.time_units.len(), 10);
        assert_eq!(
            custom
                .time_units
                .iter()
                .map(|p| p.0)
                .collect::<Vec<TimeUnit>>(),
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
        assert!(custom.time_units.iter().all(|p| p.1.is_empty()));
        assert!(custom.is_empty());
    }

    #[rstest]
    #[case::nano_second(NanoSecond, &["some"], 0)]
    #[case::nano_second_with_multiple_ids(NanoSecond, &["some", "other", "деякі"], 0)]
    #[case::micro_second(MicroSecond, &["some"], 1)]
    #[case::micro_second_with_multiple_ids(MicroSecond, &["some", "other", "деякі"], 1)]
    #[case::milli_second(MilliSecond, &["some"], 2)]
    #[case::milli_second_with_multiple_ids(MilliSecond, &["some", "other", "деякі"], 2)]
    #[case::second(Second, &["some"], 3)]
    #[case::second_with_multiple_ids(Second, &["some", "other", "деякі"], 3)]
    #[case::minute(Minute, &["some"], 4)]
    #[case::minute_with_multiple_ids(Minute, &["some", "other", "деякі"], 4)]
    #[case::hour(Hour, &["some"], 5)]
    #[case::hour_with_multiple_ids(Hour, &["some", "other", "деякі"], 5)]
    #[case::day(Day, &["some"], 6)]
    #[case::day_with_multiple_ids(Day, &["some", "other", "деякі"], 6)]
    #[case::week(Week, &["some"], 7)]
    #[case::week_with_multiple_ids(Week, &["some", "other", "деякі"], 7)]
    #[case::month(Month, &["some"], 8)]
    #[case::month_with_multiple_ids(Month, &["some", "other", "деякі"], 8)]
    #[case::year(Year, &["some"], 9)]
    #[case::year_with_multiple_ids(Year, &["some", "other", "деякі"], 9)]
    fn test_custom_time_units_init_with_time_units(
        #[case] time_unit: TimeUnit,
        #[case] ids: &[&str],
        #[case] expected_index: usize,
    ) {
        let custom = CustomTimeUnits::with_time_units(&[(time_unit, ids)]);

        assert!(!custom.is_empty());
        assert_eq!(
            custom.time_units.get(expected_index),
            Some(&(time_unit, Vec::from(ids)))
        );
        assert_eq!(
            CustomTimeUnits::map_time_unit_to_index(time_unit),
            expected_index
        );
        assert_eq!(custom.get_time_units(), vec![time_unit]);
    }

    #[test]
    fn test_custom_time_units_init_with_time_units_when_multiple_equal_ids() {
        let custom = CustomTimeUnits::with_time_units(&[(NanoSecond, &["same", "same"])]);
        assert!(!custom.is_empty());
        assert_eq!(custom.get_time_units(), vec![NanoSecond]);
        assert_eq!(custom.get("same"), Some(NanoSecond));
    }

    #[test]
    fn test_custom_time_units_when_add_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((MicroSecond, &["some", "ids"]));
        assert!(custom
            .time_units
            .iter()
            .filter(|p| p.0 != MicroSecond)
            .all(|p| p.1.is_empty()));
        assert_eq!(
            custom
                .time_units
                .get(CustomTimeUnits::map_time_unit_to_index(MicroSecond)),
            Some(&(MicroSecond, vec!["some", "ids"]))
        );
        assert_eq!(custom.get("some"), Some(MicroSecond));
        assert_eq!(custom.get("ids"), Some(MicroSecond));
        assert_eq!(custom.get("does not exist"), None);
        assert!(!custom.is_empty());
    }

    #[test]
    fn test_custom_time_units_when_adding_time_unit_with_empty_slice_then_not_added() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((MicroSecond, &[]));
        assert!(custom.is_empty());
        assert_eq!(custom.get_time_units(), vec![]);
    }

    #[test]
    fn test_custom_time_units_when_adding_time_unit_with_empty_id_then_not_added() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((MicroSecond, &[""]));
        assert!(custom.is_empty());
        assert_eq!(custom.get_time_units(), vec![]);
    }

    #[test]
    fn test_custom_duration_parser_init_new() {
        let parser = CustomDurationParser::new();
        assert_eq!(parser.default_unit, Second);
        assert!(parser.time_units.is_empty());
        assert_eq!(parser.get_current_time_units(), vec![]);
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
        let parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
        assert_eq!(parser.default_unit, Second);
        assert_eq!(
            Vec::from(parser.time_units.time_units.as_slice()),
            DEFAULT_TIME_UNITS
                .iter()
                .map(|(t, v)| (*t, Vec::from(*v)))
                .collect::<Vec<(TimeUnit, Vec<&str>)>>()
        );
        assert_eq!(
            parser.get_current_time_units(),
            DEFAULT_TIME_UNITS
                .iter()
                .map(|(t, _)| *t)
                .collect::<Vec<TimeUnit>>()
        );
        assert_eq!(parser.parse("1.0"), Ok(Duration::new(1, 0)));
    }

    #[test]
    fn test_custom_duration_parser_init_default() {
        let parser = CustomDurationParser::default();
        assert!(parser.time_units.is_empty());
        assert_eq!(parser.get_current_time_units(), vec![]);
    }

    #[test]
    fn test_custom_duration_parser_when_add_time_unit() {
        let mut parser = CustomDurationParser::new();
        parser.time_unit(NanoSecond, &["nanos"]);
        assert!(!parser.time_units.is_empty());
        assert_eq!(
            Vec::from_iter(
                parser
                    .time_units
                    .time_units
                    .iter()
                    .filter(|(_, v)| !v.is_empty())
            ),
            vec![&(NanoSecond, vec!["nanos"])]
        );
        assert_eq!(parser.get_current_time_units(), vec![NanoSecond]);
    }

    #[test]
    fn test_custom_duration_parser_when_add_time_units() {
        let mut parser = CustomDurationParser::new();
        parser.time_units(&[(NanoSecond, &["ns", "nanos"]), (MilliSecond, &["ms"])]);
        assert_eq!(
            Vec::from_iter(
                parser
                    .time_units
                    .time_units
                    .iter()
                    .filter(|(_, v)| !v.is_empty())
            ),
            vec![
                &(NanoSecond, vec!["ns", "nanos"]),
                &(MilliSecond, vec!["ms"])
            ]
        );
        assert_eq!(
            parser.get_current_time_units(),
            vec![NanoSecond, MilliSecond]
        );
    }

    #[test]
    fn test_custom_duration_parser_when_setting_default_time_unit() {
        let mut parser = CustomDurationParser::new();
        parser.default_unit(NanoSecond);

        assert_eq!(parser.default_unit, NanoSecond);
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
        let parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
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
}
