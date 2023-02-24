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

/// Part of the `custom` feature with [`TimeUnit`] ids as defined in
/// [`systemd.time`](https://www.man7.org/linux/man-pages/man7/systemd.time.7.html)
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
/// without `Month` and `Year`.
pub const DEFAULT_TIME_UNITS: [(TimeUnit, &[&str]); 8] = [
    (NanoSecond, &[DEFAULT_ID_NANO_SECOND]),
    (MicroSecond, &[DEFAULT_ID_MICRO_SECOND]),
    (MilliSecond, &[DEFAULT_ID_MILLI_SECOND]),
    (Second, &[DEFAULT_ID_SECOND]),
    (Minute, &[DEFAULT_ID_MINUTE]),
    (Hour, &[DEFAULT_ID_HOUR]),
    (Day, &[DEFAULT_ID_DAY]),
    (Week, &[DEFAULT_ID_WEEK]),
];

/// Part of the `custom` feature with all [`TimeUnit`] ids as defined in the `default` feature.
pub const DEFAULT_ALL_TIME_UNITS: [(TimeUnit, &[&str]); 10] = [
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

type Identifiers<'a> = (LookupData, Vec<&'a str>);
type IdentifiersSlice<'a> = (TimeUnit, &'a [&'a str]);

#[derive(Debug)]
struct CustomTimeUnits<'a> {
    min_length: usize,
    max_length: usize,
    time_units: [Identifiers<'a>; 10],
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct LookupData {
    min_length: usize,
    max_length: usize,
    time_unit: TimeUnit,
}

impl LookupData {
    fn new(time_unit: TimeUnit) -> Self {
        Self {
            min_length: usize::MAX,
            max_length: 0,
            time_unit,
        }
    }

    fn update(&mut self, identifier: &str) {
        let len = identifier.len();
        if self.min_length > len {
            self.min_length = len;
        }
        if self.max_length < len {
            self.max_length = len;
        }
    }

    fn check(&self, identifier: &str) -> bool {
        let len = identifier.len();
        self.min_length <= len && self.max_length >= len
    }

    fn is_empty(&self) -> bool {
        self.min_length == usize::MAX && self.max_length == 0
    }
}

impl<'a> CustomTimeUnits<'a> {
    fn new() -> Self {
        Self::with_capacity(0)
    }

    fn with_time_units(units: &[IdentifiersSlice<'a>]) -> Self {
        let capacity = units.iter().fold(0, |a, (_, v)| a.max(v.len()));
        let mut time_units = Self::with_capacity(capacity);
        time_units.add_time_units(units);
        time_units
    }

    fn add_time_unit(&mut self, unit: IdentifiersSlice<'a>) {
        let (time_unit, other) = unit;
        if other.is_empty() {
            return;
        }
        let (data, ids) = self.lookup_mut(time_unit);

        for &id in other.iter().filter(|&&id| !id.is_empty()) {
            ids.push(id);
            data.update(id);
        }
        let min_length = data.min_length;
        let max_length = data.max_length;
        self.update_lengths(min_length, max_length);
    }

    fn add_time_units(&mut self, units: &[IdentifiersSlice<'a>]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }
    fn with_capacity(capacity: usize) -> Self {
        Self {
            min_length: usize::MAX,
            max_length: 0,
            time_units: [
                (LookupData::new(NanoSecond), Vec::with_capacity(capacity)),
                (LookupData::new(MicroSecond), Vec::with_capacity(capacity)),
                (LookupData::new(MilliSecond), Vec::with_capacity(capacity)),
                (LookupData::new(Second), Vec::with_capacity(capacity)),
                (LookupData::new(Minute), Vec::with_capacity(capacity)),
                (LookupData::new(Hour), Vec::with_capacity(capacity)),
                (LookupData::new(Day), Vec::with_capacity(capacity)),
                (LookupData::new(Week), Vec::with_capacity(capacity)),
                (LookupData::new(Month), Vec::with_capacity(capacity)),
                (LookupData::new(Year), Vec::with_capacity(capacity)),
            ],
        }
    }

    fn lookup_mut(&'_ mut self, unit: TimeUnit) -> &'_ mut (LookupData, Vec<&'a str>) {
        &mut self.time_units[unit as usize]
    }

    fn update_lengths(&mut self, min_length: usize, max_length: usize) {
        if self.min_length > min_length {
            self.min_length = min_length;
        }
        if self.max_length < max_length {
            self.max_length = max_length;
        }
    }

    fn get_time_units(&self) -> Vec<TimeUnit> {
        self.time_units
            .iter()
            .filter_map(|(data, _)| {
                if !data.is_empty() {
                    Some(data.time_unit)
                } else {
                    None
                }
            })
            .collect()
    }
}

impl<'a> TimeUnitsLike<IdentifiersSlice<'a>> for CustomTimeUnits<'a> {
    fn is_empty(&self) -> bool {
        self.time_units.iter().all(|(_, v)| v.is_empty())
    }

    fn get(&self, identifier: &str) -> Option<TimeUnit> {
        let len = identifier.len();
        if self.min_length > len || self.max_length < len {
            return None;
        }
        self.time_units.iter().find_map(|(data, v)| {
            if data.check(identifier) && v.contains(&identifier) {
                Some(data.time_unit)
            } else {
                None
            }
        })
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
    /// [`CustomDurationParser::with_time_units`] which initializes the parser with a set time units
    /// with custom `ids`. The default time unit can be changed with
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
                .map(|(data, _)| data.time_unit)
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
    #[case::nano_second(NanoSecond, &["some"], 4, 4)]
    #[case::nano_second_with_multiple_ids(NanoSecond, &["some", "other", "деякі"], 4, 10)]
    #[case::micro_second(MicroSecond, &["some"], 4, 4)]
    #[case::micro_second_with_multiple_ids(MicroSecond, &["some", "other", "деякі"], 4, 10)]
    #[case::milli_second(MilliSecond, &["some"], 4, 4)]
    #[case::milli_second_with_multiple_ids(MilliSecond, &["some", "other", "деякі"], 4, 10)]
    #[case::second(Second, &["some"], 4, 4)]
    #[case::second_with_multiple_ids(Second, &["some", "other", "деякі"], 4, 10)]
    #[case::minute(Minute, &["some"], 4, 4)]
    #[case::minute_with_multiple_ids(Minute, &["some", "other", "деякі"], 4, 10)]
    #[case::hour(Hour, &["some"], 4, 4)]
    #[case::hour_with_multiple_ids(Hour, &["some", "other", "деякі"], 4, 10)]
    #[case::day(Day, &["some"], 4, 4)]
    #[case::day_with_multiple_ids(Day, &["some", "other", "деякі"], 4, 10)]
    #[case::week(Week, &["some"], 4, 4)]
    #[case::week_with_multiple_ids(Week, &["some", "other", "деякі"], 4, 10)]
    #[case::month(Month, &["some"], 4, 4)]
    #[case::month_with_multiple_ids(Month, &["some", "other", "деякі"], 4, 10)]
    #[case::year(Year, &["some"], 4, 4)]
    #[case::year_with_multiple_ids(Year, &["some", "other", "деякі"], 4, 10)]
    fn test_custom_time_units_init_with_time_units(
        #[case] time_unit: TimeUnit,
        #[case] ids: &[&str],
        #[case] min_length: usize,
        #[case] max_length: usize,
    ) {
        let mut custom = CustomTimeUnits::with_time_units(&[(time_unit, ids)]);

        assert!(!custom.is_empty());
        assert_eq!(
            custom.lookup_mut(time_unit),
            &(
                LookupData {
                    min_length,
                    max_length,
                    time_unit
                },
                Vec::from(ids)
            )
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
            .filter(|(data, _)| data.time_unit != MicroSecond)
            .all(|(_, v)| v.is_empty()));
        assert_eq!(custom.lookup_mut(MicroSecond).1, vec!["some", "ids"]);
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
        let parser = CustomDurationParser::with_time_units(&DEFAULT_ALL_TIME_UNITS);
        assert_eq!(parser.default_unit, Second);
        assert_eq!(
            Vec::from(parser.time_units.time_units.as_slice()),
            DEFAULT_ALL_TIME_UNITS
                .iter()
                .map(|(t, v)| (
                    LookupData {
                        min_length: v[0].len(),
                        max_length: v[0].len(),
                        time_unit: *t
                    },
                    Vec::from(*v)
                ))
                .collect::<Vec<(LookupData, Vec<&str>)>>()
        );
        assert_eq!(
            parser.get_current_time_units(),
            DEFAULT_ALL_TIME_UNITS
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
            Vec::from_iter(parser.time_units.time_units.iter().filter_map(|(d, v)| {
                if !v.is_empty() {
                    Some((d.time_unit, v))
                } else {
                    None
                }
            })),
            vec![(NanoSecond, &vec!["nanos"])]
        );
        assert_eq!(parser.get_current_time_units(), vec![NanoSecond]);
    }

    #[test]
    fn test_custom_duration_parser_when_add_time_units() {
        let mut parser = CustomDurationParser::new();
        parser.time_units(&[(NanoSecond, &["ns", "nanos"]), (MilliSecond, &["ms"])]);
        assert_eq!(
            Vec::from_iter(parser.time_units.time_units.iter().filter_map(|(d, v)| {
                if !v.is_empty() {
                    Some((d.time_unit, v))
                } else {
                    None
                }
            })),
            vec![
                (NanoSecond, &vec!["ns", "nanos"]),
                (MilliSecond, &vec!["ms"])
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
}
