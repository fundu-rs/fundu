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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct LookupData {
    min_length: usize,
    max_length: usize,
    time_unit: TimeUnit,
    multiplier: Multiplier,
}

impl LookupData {
    fn new(time_unit: TimeUnit) -> Self {
        Self::with_multiplier(time_unit, Multiplier::default())
    }

    fn with_multiplier(time_unit: TimeUnit, multiplier: Multiplier) -> Self {
        Self {
            min_length: usize::MAX,
            max_length: 0,
            time_unit,
            multiplier,
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

#[derive(Debug)]
struct CustomTimeUnits<'a> {
    min_length: usize,
    max_length: usize,
    time_units: [Identifiers<'a>; 10],
    custom_time_units: Vec<Identifiers<'a>>,
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

    fn add_custom_time_unit(
        &mut self,
        base_unit: TimeUnit,
        multiplier: Multiplier,
        identifiers: &[&'a str],
    ) {
        if identifiers.is_empty() {
            return;
        }
        let (min_length, max_length) = match self.lookup_custom_mut(base_unit, multiplier) {
            Some((data, ids)) => {
                for &id in identifiers.iter().filter(|&&id| !id.is_empty()) {
                    ids.push(id);
                    data.update(id);
                }
                (data.min_length, data.max_length)
            }
            None => {
                let mut data = LookupData::with_multiplier(base_unit, multiplier);
                let mut ids = Vec::with_capacity(identifiers.len());
                for &id in identifiers.iter().filter(|&&id| !id.is_empty()) {
                    ids.push(id);
                    data.update(id);
                }
                let lengths = (data.min_length, data.max_length);
                self.custom_time_units.push((data, ids));
                lengths
            }
        };
        self.update_lengths(min_length, max_length);
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
            custom_time_units: Vec::with_capacity(capacity),
        }
    }

    fn lookup_mut(&'_ mut self, unit: TimeUnit) -> &'_ mut (LookupData, Vec<&'a str>) {
        &mut self.time_units[unit as usize]
    }

    fn lookup_custom_mut(
        &'_ mut self,
        unit: TimeUnit,
        multiplier: Multiplier,
    ) -> Option<&'_ mut (LookupData, Vec<&'a str>)> {
        self.custom_time_units
            .iter_mut()
            .find(|(data, _)| data.time_unit == unit && data.multiplier == multiplier)
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
            .chain(self.custom_time_units.iter())
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

impl<'a> TimeUnitsLike for CustomTimeUnits<'a> {
    fn is_empty(&self) -> bool {
        self.time_units
            .iter()
            .chain(self.custom_time_units.iter())
            .all(|(_, v)| v.is_empty())
    }

    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        let len = identifier.len();
        if self.min_length > len || self.max_length < len {
            return None;
        }
        self.time_units
            .iter()
            .chain(self.custom_time_units.iter())
            .find_map(|(data, v)| {
                if data.check(identifier) && v.contains(&identifier) {
                    Some((data.time_unit, data.multiplier))
                } else {
                    None
                }
            })
    }
}

/// A parser with a customizable set of [`TimeUnit`]s and customizable identifiers.
pub struct CustomDurationParser<'a> {
    time_units: CustomTimeUnits<'a>,
    inner: Parser,
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
    /// use std::time::Duration;
    ///
    /// use fundu::CustomDurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// let mut parser = CustomDurationParser::new();
    /// assert_eq!(parser.get_current_time_units(), vec![]);
    ///
    /// assert_eq!(parser.parse("100.0").unwrap(), Duration::new(100, 0));
    ///
    /// parser.default_unit(Minute);
    /// assert_eq!(parser.parse("1.0e2").unwrap(), Duration::new(6000, 0));
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
    /// [`TimeUnit`] just leave it out of the `units`. Be aware, that this library does not check
    /// the validity of identifiers, so besides the need to be a valid `utf-8` sequence there are no
    /// other limitations. There is also no check for duplicate `ids`, and empty `ids` are ignored.
    /// Note the ids for time units are case sensitive.
    ///
    /// You may find it helpful to start with a pre-defined custom sets of [`TimeUnit`]:
    /// * [`SYSTEMD_TIME_UNITS`]: This is the set of time units as specified in the [`systemd.time`](https://www.man7.org/linux/man-pages/man7/systemd.time.7.html)
    ///   documentation
    /// * [`DEFAULT_TIME_UNITS`]: This is the complete set of time units with their default ids as
    ///   used the standard crate by [`crate::DurationParser`]
    ///
    /// # Problems
    ///
    /// It's possible to choose identifiers very freely in the `utf-8` range but some identifiers
    /// interact badly with the parser and may lead to unexpected results, if they start with:
    ///
    /// * `e` or `E` which is also indicating an exponent. If
    /// [`CustomDurationParser::disable_exponent`] is set this problem does not occur.
    /// * ascii digits from `0` to `9`
    /// * decimal point `.` which is also indicating a fraction. If
    /// [`CustomDurationParser::disable_fraction`] is set, this problem does not occur
    /// * `+`, `-` which is used for signs.
    ///
    /// # Security
    ///
    /// If there is the intention to expose defining of [`TimeUnit`]s to an untrusted source, it's
    /// maybe better to limit the possible characters to something like [`char::is_alphabetic`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::CustomDurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&[
    ///     (Second, &["s"]),
    ///     (Minute, &["Min"]),
    ///     (Hour, &["ώρα"]),
    /// ]);
    /// assert_eq!(parser.get_current_time_units(), vec![Second, Minute, Hour]);
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

    /// Allow spaces between the number and the [`TimeUnit`].
    ///
    /// See also [`DurationParser::allow_spaces`].
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
    ///     Err(ParseError::Syntax(3, "No spaces allowed".to_string()))
    /// );
    ///
    /// parser.allow_spaces();
    /// assert_eq!(parser.parse("123 ns"), Ok(Duration::new(0, 123)));
    /// assert_eq!(parser.parse("123 "), Ok(Duration::new(123, 0)));
    /// ```
    ///
    /// [`DurationParser::allow_spaces`]: crate::DurationParser::allow_spaces
    pub fn allow_spaces(&mut self) -> &mut Self {
        self.inner.config.allow_spaces = true;
        self
    }

    /// Disable parsing the exponent.
    ///
    /// See also [`DurationParser::disable_exponent`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, ParseError, DEFAULT_TIME_UNITS};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
    /// parser.disable_exponent();
    /// assert_eq!(
    ///     parser.parse("123e+1"),
    ///     Err(ParseError::Syntax(3, "No exponent allowed".to_string()))
    /// );
    /// ```
    ///
    /// [`DurationParser::disable_exponent`]: crate::DurationParser::disable_exponent
    pub fn disable_exponent(&mut self) -> &mut Self {
        self.inner.config.disable_exponent = true;
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
    ///
    /// [`DurationParser::disable_fraction`]: [`crate::DurationParser::disable_fraction`]
    pub fn disable_fraction(&mut self) -> &mut Self {
        self.inner.config.disable_fraction = true;
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
    ///
    /// [`DurationParser::number_is_optional`]: [`crate::DurationParser::number_is_optional`]
    pub fn number_is_optional(&mut self) -> &mut Self {
        self.inner.config.number_is_optional = true;
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
    /// use std::time::Duration;
    ///
    /// use fundu::CustomDurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// let mut parser = CustomDurationParser::new();
    /// parser.time_unit(Minute, &["minutes", "λεπτό"]);
    ///
    /// assert_eq!(parser.parse("42minutes").unwrap(), Duration::new(2520, 0));
    ///
    /// assert_eq!(parser.parse("42λεπτό").unwrap(), Duration::new(2520, 0));
    ///
    /// assert!(parser.parse("42Minutes").is_err());
    ///
    /// parser.time_unit(Minute, &["Minutes"]);
    ///
    /// assert_eq!(parser.parse("42Minutes").unwrap(), Duration::new(2520, 0));
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
    /// use std::time::Duration;
    ///
    /// use fundu::CustomDurationParser;
    /// use fundu::TimeUnit::*;
    ///
    /// let mut parser = CustomDurationParser::new();
    /// assert_eq!(
    ///     parser
    ///         .time_units(&[(MicroSecond, &["µ", "Ms"]), (Second, &["s", "seconds"])])
    ///         .parse("1µ")
    ///         .unwrap(),
    ///     Duration::new(0, 1000),
    /// );
    /// ```
    pub fn time_units(&mut self, units: &'a [IdentifiersSlice]) -> &mut Self {
        self.time_units.add_time_units(units);
        self
    }

    /// Add a custom time unit to the current set of [`TimeUnit`]s.
    ///
    /// Custom time units have a base [`TimeUnit`] and a [`Multiplier`] in addition to their
    /// identifiers.
    ///
    /// # Problems
    ///
    /// Don't use a [`Multiplier`] to get lower than [`TimeUnit::NanoSecond`] (=Multiplier(1, -9))
    /// or higher than [`u64::MAX`]. Such multipliers may lead to unexpected results or even panics
    /// in other parts of the program.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, Multiplier};
    ///
    /// let mut parser = CustomDurationParser::new();
    /// parser
    ///     .custom_time_unit(Week, Multiplier(2, 0), &["fortnight", "fortnights"])
    ///     .custom_time_unit(
    ///         Second,
    ///         Multiplier(1000, 0),
    ///         &["kilosecond", "kiloseconds", "kilos"],
    ///     )
    ///     .custom_time_unit(Second, Multiplier(1, -8), &["shakes"]);
    /// assert_eq!(
    ///     parser.parse("1fortnights").unwrap(),
    ///     Duration::new(2 * 7 * 24 * 60 * 60, 0),
    /// );
    /// ```
    ///
    /// The `base_unit` is only used to calculate the final time span and does not need to be unique
    /// in the set of time units. It's even possible to define an own time unit for example for a
    /// definition of a [`TimeUnit::Year`] either in addition or as a replacement of the year
    /// definition of this crate (=`365.25` days).
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, Multiplier, DEFAULT_TIME_UNITS};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
    /// // The common year is usually defined as 365 days
    /// parser.custom_time_unit(Day, Multiplier(356, 0), &["y", "year", "years"]);
    /// assert_eq!(
    ///     parser.parse("1year").unwrap(),
    ///     Duration::new(356 * 24 * 60 * 60, 0),
    /// );
    /// ```
    pub fn custom_time_unit(
        &mut self,
        base_unit: TimeUnit,
        multiplier: Multiplier,
        identifiers: &[&'a str],
    ) -> &mut Self {
        self.time_units
            .add_custom_time_unit(base_unit, multiplier, identifiers);
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
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     CustomDurationParser::new().parse("1.2e-1").unwrap(),
    ///     Duration::new(0, 120_000_000),
    /// );
    /// ```
    #[inline(never)]
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
    /// use fundu::TimeUnit::*;
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
    #[inline(never)]
    pub fn parse_negative(&self, source: &str) -> Result<time::Duration, ParseError> {
        self.inner.parse_negative(source, &self.time_units)
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

    const YEAR: u64 = 60 * 60 * 24 * 365 + 60 * 60 * 24 / 4;
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
                    time_unit,
                    multiplier: Multiplier::default()
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
        assert_eq!(
            custom.get("same"),
            Some((NanoSecond, Multiplier::default()))
        );
    }

    #[test]
    fn test_custom_time_units_when_add_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((MicroSecond, &["some", "ids"]));
        assert!(
            custom
                .time_units
                .iter()
                .filter(|(data, _)| data.time_unit != MicroSecond)
                .all(|(_, v)| v.is_empty())
        );
        assert_eq!(custom.lookup_mut(MicroSecond).1, vec!["some", "ids"]);
        assert_eq!(
            custom.get("some"),
            Some((MicroSecond, Multiplier::default()))
        );
        assert_eq!(
            custom.get("ids"),
            Some((MicroSecond, Multiplier::default()))
        );
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
    fn test_custom_time_units_adding_custom_time_unit_with_empty_id_then_not_added() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(Second, Multiplier(2, 0), &[""]);
        assert!(custom.is_empty());
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(Second, Multiplier(2, 0), &["sec"]);
        assert!(!custom.is_empty());
        assert_eq!(custom.get_time_units(), vec![Second]);
        assert_eq!(custom.get("sec"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_multiple_custom_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(Second, Multiplier(1, 0), &["sec"]);
        custom.add_custom_time_unit(Second, Multiplier(2, 0), &["secs"]);
        assert_eq!(custom.get_time_units(), vec![Second, Second]);
        assert_eq!(custom.get("sec"), Some((Second, Multiplier(1, 0))));
        assert_eq!(custom.get("secs"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_normal_time_unit_already_exists() {
        let mut custom = CustomTimeUnits::with_time_units(&[(Second, &["s"])]);
        custom.add_custom_time_unit(Second, Multiplier(2, 0), &["ss"]);
        assert_eq!(custom.get_time_units(), vec![Second, Second]);
        assert_eq!(custom.get("s"), Some((Second, Multiplier(1, 0))));
        assert_eq!(custom.get("ss"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_normal_time_unit_with_same_id() {
        let mut custom = CustomTimeUnits::with_time_units(&[(Second, &["s"])]);
        custom.add_custom_time_unit(Second, Multiplier(2, 0), &["s"]);
        assert_eq!(custom.get_time_units(), vec![Second, Second]);
        assert_eq!(custom.get("s"), Some((Second, Multiplier(1, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_identifiers_is_empty() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(Second, Multiplier(2, 0), &[]);
        assert_eq!(custom.get_time_units(), vec![]);
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_adding_same_unit_twice() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(Second, Multiplier(2, 0), &["s"]);
        custom.add_custom_time_unit(Second, Multiplier(2, 0), &["s"]);
        assert_eq!(custom.get_time_units(), vec![Second]);
    }

    #[test]
    fn test_custom_duration_parser_init_new() {
        let parser = CustomDurationParser::new();
        assert_eq!(parser.inner.config.default_unit, Second);
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
        assert_eq!(parser.inner.config.default_unit, Second);
        assert_eq!(
            Vec::from(parser.time_units.time_units.as_slice()),
            DEFAULT_ALL_TIME_UNITS
                .iter()
                .map(|(t, v)| (
                    LookupData {
                        min_length: v[0].len(),
                        max_length: v[0].len(),
                        time_unit: *t,
                        multiplier: Multiplier::default()
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
    fn test_custom_duration_parser_when_add_custom_time_units() {
        let mut parser = CustomDurationParser::new();
        parser.custom_time_unit(Year, Multiplier(100, 0), &["century", "centuries"]);
        assert_eq!(parser.get_current_time_units(), vec![Year]);
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
        parser.allow_spaces();
        assert!(parser.inner.config.allow_spaces);
    }

    #[test]
    fn test_custom_duration_parser_setting_disable_fraction() {
        let mut parser = CustomDurationParser::new();
        parser.disable_fraction();
        assert!(parser.inner.config.disable_fraction);
    }

    #[test]
    fn test_custom_duration_parser_setting_disable_exponent() {
        let mut parser = CustomDurationParser::new();
        parser.disable_exponent();
        assert!(parser.inner.config.disable_exponent);
    }

    #[test]
    fn test_custom_duration_parser_setting_number_is_optional() {
        let mut parser = CustomDurationParser::new();
        parser.number_is_optional();
        assert!(parser.inner.config.number_is_optional);
    }
}
