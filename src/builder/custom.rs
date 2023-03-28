// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use super::config::Config;
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
    fn new(time_unit: TimeUnit, multiplier: Multiplier) -> Self {
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
}

/// A [`CustomTimeUnit`] is a completely customizable [`TimeUnit`] using an additional
/// [`Multiplier`].
///
/// Custom time units have a base [`TimeUnit`] (which has an inherent [`Multiplier`]) and an
/// optional [`Multiplier`] which acts as an additional [`Multiplier`] to the multiplier of the
/// `base_unit`. Using a multiplier with `Multiplier(1, 0)` is equivalent to using no multiplier
/// at all. A [`CustomTimeUnit`] also consists of identifiers which are used to identify the
/// [`CustomTimeUnit`] during the parsing process.
///
/// To create a [`CustomTimeUnit`] representing two weeks there are multiple (almost countless)
/// solutions. Just to show two very obvious examples:
///
/// ```rust
/// use fundu::TimeUnit::*;
/// use fundu::{CustomTimeUnit, Multiplier};
///
/// assert_ne!(
///     (CustomTimeUnit::new(Week, &["fortnight", "fortnights"], Some(Multiplier(2, 0)))),
///     (CustomTimeUnit::new(Day, &["fortnight", "fortnights"], Some(Multiplier(14, 0))))
/// );
/// ```
///
/// Both would actually be equal in the sense, that they would resolve to the same result when
/// multiplying the `base_unit` with the `multiplier`, however they are treated as not equal and
/// it's possible to choose freely between the definitions. Using both of the definitions in
/// parallel within the [`CustomDurationParser`] would be possible and produces the desired
/// result, although it does not provide any benefits.
///
/// ```rust
/// use std::time::Duration;
///
/// use fundu::TimeUnit::*;
/// use fundu::{CustomDurationParser, CustomTimeUnit, Multiplier};
///
/// let parser = CustomDurationParser::builder()
///     .custom_time_units(&[
///         CustomTimeUnit::new(Week, &["fortnight", "fortnights"], Some(Multiplier(2, 0))),
///         CustomTimeUnit::new(Day, &["fortnight", "fortnights"], Some(Multiplier(14, 0))),
///     ])
///     .build();
///
/// assert_eq!(
///     parser.parse("1fortnight").unwrap(),
///     Duration::new(1209600, 0)
/// );
/// ```
///
/// In summary, the best choice is to use the [`CustomTimeUnit`] with a `base_unit` having the
/// lowest [`Multiplier`].
///
/// Equality of two [`CustomTimeUnit`] is defined as
///
/// ```ignore
/// base_unit == other.base_unit && multiplier == other.multiplier
/// ```
#[derive(Debug, Eq, Clone, Copy)]
pub struct CustomTimeUnit<'a> {
    base_unit: TimeUnit,
    multiplier: Multiplier,
    identifiers: &'a [&'a str],
}

impl<'a> PartialEq for CustomTimeUnit<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.base_unit == other.base_unit && self.multiplier == other.multiplier
    }
}

impl<'a> CustomTimeUnit<'a> {
    /// Create a new [`CustomTimeUnit`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, CustomTimeUnit, Multiplier};
    ///
    /// let time_unit = CustomTimeUnit::new(Second, &["shake", "shakes"], Some(Multiplier(1, -8)));
    /// let parser = CustomDurationParser::builder()
    ///     .custom_time_unit(time_unit)
    ///     .build();
    ///
    /// assert_eq!(parser.parse("1shake").unwrap(), Duration::new(0, 10));
    /// ```
    pub const fn new(
        base_unit: TimeUnit,
        identifiers: &'a [&'a str],
        multiplier: Option<Multiplier>,
    ) -> Self {
        Self {
            base_unit,
            multiplier: match multiplier {
                Some(m) => m,
                None => Multiplier(1, 0),
            },
            identifiers,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct CustomTimeUnits<'a> {
    min_length: usize,
    max_length: usize,
    time_units: Vec<Identifiers<'a>>,
}

impl<'a> CustomTimeUnits<'a> {
    fn new() -> Self {
        Self::with_capacity(0)
    }

    fn with_time_units(units: &[IdentifiersSlice<'a>]) -> Self {
        let mut time_units = Self::with_capacity(units.len());
        time_units.add_time_units(units);
        time_units
    }

    fn with_capacity(capacity: usize) -> Self {
        Self {
            min_length: usize::MAX,
            max_length: 0,
            time_units: Vec::with_capacity(capacity),
        }
    }

    fn add_time_unit(&mut self, unit: IdentifiersSlice<'a>) {
        let (time_unit, identifiers) = unit;
        self.add_custom_time_unit(CustomTimeUnit::new(time_unit, identifiers, None));
    }

    fn add_time_units(&mut self, units: &[IdentifiersSlice<'a>]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    fn add_custom_time_unit(&mut self, time_unit: CustomTimeUnit<'a>) {
        if time_unit.identifiers.is_empty() {
            return;
        }
        let CustomTimeUnit {
            base_unit,
            multiplier,
            identifiers,
        } = time_unit;
        let (min_length, max_length) = match self.lookup_mut(base_unit, multiplier) {
            Some((data, ids)) => {
                for &identifier in identifiers.iter().filter(|&&id| !id.is_empty()) {
                    ids.push(identifier);
                    data.update(identifier);
                }
                (data.min_length, data.max_length)
            }
            None => {
                let mut data = LookupData::new(base_unit, multiplier);
                let mut ids = Vec::with_capacity(identifiers.len());
                for &identifier in identifiers.iter().filter(|&&id| !id.is_empty()) {
                    ids.push(identifier);
                    data.update(identifier);
                }
                if ids.is_empty() {
                    return;
                }
                let lengths = (data.min_length, data.max_length);
                self.time_units.push((data, ids));
                lengths
            }
        };
        self.update_lengths(min_length, max_length);
    }

    fn lookup_mut(
        &'_ mut self,
        unit: TimeUnit,
        multiplier: Multiplier,
    ) -> Option<&'_ mut (LookupData, Vec<&'a str>)> {
        self.time_units
            .iter_mut()
            .find(|(data, _)| data.time_unit == unit && data.multiplier == multiplier)
    }

    #[allow(dead_code)]
    fn lookup(
        &self,
        unit: TimeUnit,
        multiplier: Multiplier,
    ) -> Option<&(LookupData, Vec<&'a str>)> {
        self.time_units
            .iter()
            .find(|(data, _)| data.time_unit == unit && data.multiplier == multiplier)
    }

    fn find_id(&self, id: &str) -> Option<(TimeUnit, Multiplier)> {
        self.time_units.iter().find_map(|(data, v)| {
            if data.check(id) && v.contains(&id) {
                Some((data.time_unit, data.multiplier))
            } else {
                None
            }
        })
    }

    fn update_lengths(&mut self, min_length: usize, max_length: usize) {
        if self.min_length > min_length {
            self.min_length = min_length;
        }
        if self.max_length < max_length {
            self.max_length = max_length;
        }
    }
}

impl<'a> TimeUnitsLike for CustomTimeUnits<'a> {
    fn is_empty(&self) -> bool {
        self.time_units.is_empty()
    }

    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        let len = identifier.len();
        if self.min_length > len || self.max_length < len {
            return None;
        }
        self.find_id(identifier)
    }
}

/// A parser with a customizable set of [`TimeUnit`]s and customizable identifiers.
#[derive(Debug, PartialEq, Eq)]
pub struct CustomDurationParser<'a> {
    time_units: CustomTimeUnits<'a>,
    inner: Parser,
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
    /// use fundu::TimeUnit::*;
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
    /// [`TimeUnit`] just leave it out of the `units`. Be aware, that this library does not check
    /// the validity of identifiers, so besides the need to be a valid `utf-8` sequence there are no
    /// other limitations. There is also no check for duplicate `ids` but empty `ids` are ignored.
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
    /// It's possible to choose identifiers very freely within the `utf-8` range. However, some
    /// identifiers interact badly with the parser and may lead to unexpected results if they
    /// start with:
    ///
    /// * `e` or `E` which is also indicating an exponent. If
    /// [`CustomDurationParser::disable_exponent`] is set this problem does not occur.
    /// * ascii digits from `0` to `9`
    /// * decimal point `.` which is also indicating a fraction. If
    /// [`CustomDurationParser::disable_fraction`] is set, this problem does not occur
    /// * `+`, `-` which is used for signs.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, Multiplier};
    ///
    /// let mut parser = CustomDurationParser::with_time_units(&[
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
    ///     .allow_spaces()
    ///     .build();
    ///
    /// assert_eq!(parser.parse("1 ns").unwrap(), Duration::new(0, 1));
    /// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
    ///
    /// // instead of
    ///
    /// let mut parser = DurationParser::with_all_time_units();
    /// parser.default_unit(MicroSecond).allow_spaces(true);
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
    /// The `base_unit` is only used to calculate the final duration and does not need to be unique
    /// in the set of time units. It's even possible to define an own time unit for example for a
    /// definition of a [`TimeUnit::Year`] either in addition or as a replacement of the year
    /// definition of this crate (Julian Year = `365.25` days).
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
    /// use fundu::TimeUnit::*;
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

    /// Allow spaces between the number and the [`TimeUnit`].
    ///
    /// See also [`crate::DurationParser::allow_spaces`].
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
    /// parser.allow_spaces(true);
    /// assert_eq!(parser.parse("123 ns"), Ok(Duration::new(0, 123)));
    /// assert_eq!(parser.parse("123 "), Ok(Duration::new(123, 0)));
    /// ```
    pub fn allow_spaces(&mut self, value: bool) -> &mut Self {
        self.inner.config.allow_spaces = value;
        self
    }

    /// Disable parsing the exponent.
    ///
    /// See also [`crate::DurationParser::disable_exponent`].
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

    /// This setting makes a number in the source string optional.
    ///
    /// See also [`crate::DurationParser::number_is_optional`].
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

    /// Try to find the [`TimeUnit`] with it's associate [`Multiplier`] by id
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
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
}

impl<'a> Default for CustomDurationParser<'a> {
    fn default() -> Self {
        Self::new()
    }
}

/// Like [`crate::DurationParserBuilder`] for [`crate::DurationParser`], this is a builder for a
/// [`CustomDurationParser`].
///
/// # Examples
///
/// ```rust
/// use std::time::Duration;
///
/// use fundu::TimeUnit::*;
/// use fundu::{CustomDurationParser, CustomDurationParserBuilder};
///
/// let parser = CustomDurationParserBuilder::new()
///     .time_units(&[(NanoSecond, &["ns"])])
///     .default_unit(MicroSecond)
///     .allow_spaces()
///     .build();
///
/// assert_eq!(parser.parse("1 ns").unwrap(), Duration::new(0, 1));
/// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
///
/// // instead of
///
/// let mut parser = CustomDurationParser::with_time_units(&[(NanoSecond, &["ns"])]);
/// parser.default_unit(MicroSecond).allow_spaces(true);
///
/// assert_eq!(parser.parse("1 ns").unwrap(), Duration::new(0, 1));
/// assert_eq!(parser.parse("1").unwrap(), Duration::new(0, 1_000));
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct CustomDurationParserBuilder<'a> {
    config: Config,
    time_units: Option<&'a [IdentifiersSlice<'a>]>,
    custom_time_units: Vec<CustomTimeUnit<'a>>,
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
    /// complicated structure of custom time units and to keep the building process as performant as
    /// possible.
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
            config: Config::new(),
            time_units: None,
            custom_time_units: vec![],
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
    pub fn time_units(mut self, time_units: &'a [IdentifiersSlice<'a>]) -> Self {
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
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, CustomTimeUnit, Multiplier};
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
    ///     Duration::new(2 * 7 * 24 * 60 * 60, 0),
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
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, CustomTimeUnit, Multiplier};
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
    ///     Duration::new(2 * 7 * 24 * 60 * 60, 0),
    /// );
    /// ```
    pub fn custom_time_units(mut self, time_units: &[CustomTimeUnit<'a>]) -> Self {
        for unit in time_units {
            self.custom_time_units.push(*unit);
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
    /// use std::time::Duration;
    ///
    /// use fundu::CustomDurationParserBuilder;
    /// use fundu::TimeUnit::*;
    ///
    /// assert_eq!(
    ///     CustomDurationParserBuilder::new()
    ///         .default_unit(NanoSecond)
    ///         .build()
    ///         .parse("42")
    ///         .unwrap(),
    ///     Duration::new(0, 42)
    /// );
    /// ```
    pub fn default_unit(mut self, unit: TimeUnit) -> Self {
        self.config.default_unit = unit;
        self
    }

    /// Allow spaces between the number and the [`TimeUnit`].
    ///
    /// See also [`crate::DurationParser::allow_spaces`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, ParseError};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&[(NanoSecond, &["ns"])])
    ///     .allow_spaces()
    ///     .build();
    ///
    /// assert_eq!(parser.parse("123 ns"), Ok(Duration::new(0, 123)));
    /// assert_eq!(parser.parse("123 "), Ok(Duration::new(123, 0)));
    /// ```
    pub fn allow_spaces(mut self) -> Self {
        self.config.allow_spaces = true;
        self
    }

    /// Disable parsing an exponent.
    ///
    /// See also [`crate::DurationParser::disable_exponent`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
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
    pub fn disable_exponent(mut self) -> Self {
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
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, ParseError};
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
    /// assert_eq!(parser.parse("123e-2"), Ok(Duration::new(1, 230_000_000)));
    /// assert_eq!(parser.parse("123ns"), Ok(Duration::new(0, 123)));
    /// ```
    pub fn disable_fraction(mut self) -> Self {
        self.config.disable_fraction = true;
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
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParserBuilder, DEFAULT_TIME_UNITS};
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&DEFAULT_TIME_UNITS)
    ///     .number_is_optional()
    ///     .build();
    ///
    /// for input in &[".001e-6s", "ns", "e-9", "e-3Ms"] {
    ///     assert_eq!(parser.parse(input), Ok(Duration::new(0, 1)));
    /// }
    /// ```
    pub fn number_is_optional(mut self) -> Self {
        self.config.number_is_optional = true;
        self
    }

    /// Finally, build the [`CustomDurationParser`] from this builder.
    ///
    /// Note this method is meant as a one-off builder method and can therefore only be used once on
    /// each [`CustomDurationParserBuilder`]. However, the parser built with this method can be used
    /// multiple times.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::CustomDurationParserBuilder;
    /// use fundu::TimeUnit::*;
    ///
    /// let parser = CustomDurationParserBuilder::new()
    ///     .time_units(&[(Minute, &["min"]), (Hour, &["h", "hr"])])
    ///     .allow_spaces()
    ///     .build();
    ///
    /// for input in &["60 min", "1h", "1 hr"] {
    ///     assert_eq!(parser.parse(input).unwrap(), Duration::new(60 * 60, 0));
    /// }
    /// ```
    pub fn build(self) -> CustomDurationParser<'a> {
        let parser = Parser::with_config(self.config);
        let mut parser = match &self.time_units {
            Some(time_units) => CustomDurationParser {
                time_units: CustomTimeUnits::with_time_units(time_units),
                inner: parser,
            },
            None => CustomDurationParser {
                time_units: CustomTimeUnits::with_capacity(self.custom_time_units.len()),
                inner: parser,
            },
        };
        parser.custom_time_units(&self.custom_time_units);
        parser
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;
    #[cfg(feature = "negative")]
    use crate::builder::config::Config;

    const YEAR: u64 = 60 * 60 * 24 * 365 + 60 * 60 * 24 / 4;
    const MONTH: u64 = YEAR / 12;

    fn make_lookup_result(
        min_length: usize,
        max_length: usize,
        time_unit: TimeUnit,
        multiplier: Multiplier,
        identifiers: Vec<&str>,
    ) -> (LookupData, Vec<&str>) {
        (
            LookupData {
                min_length,
                max_length,
                time_unit,
                multiplier,
            },
            identifiers,
        )
    }

    #[test]
    fn test_custom_time_units_init_new() {
        let custom = CustomTimeUnits::new();
        assert!(custom.time_units.is_empty());
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
        let custom = CustomTimeUnits::with_time_units(&[(time_unit, ids)]);
        assert!(!custom.is_empty());
        assert_eq!(
            custom.lookup(time_unit, Multiplier::default()),
            Some(&make_lookup_result(
                min_length,
                max_length,
                time_unit,
                Multiplier::default(),
                Vec::from(ids)
            ))
        );
    }

    #[test]
    fn test_custom_time_units_init_with_time_units_when_multiple_equal_ids() {
        let custom = CustomTimeUnits::with_time_units(&[(NanoSecond, &["same", "same"])]);
        assert!(!custom.is_empty());
        assert_eq!(
            custom.lookup(NanoSecond, Multiplier::default()),
            Some(&make_lookup_result(
                4,
                4,
                NanoSecond,
                Multiplier::default(),
                vec!["same", "same"]
            ))
        );
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
        assert_eq!(
            custom.lookup(MicroSecond, Multiplier::default()).unwrap().1,
            vec!["some", "ids"]
        );
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
        assert_eq!(custom.lookup(MicroSecond, Multiplier::default()), None);
    }

    #[test]
    fn test_custom_time_units_when_adding_time_unit_with_empty_id_then_not_added() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((MicroSecond, &[""]));
        assert!(custom.is_empty());
        assert_eq!(custom.lookup(MicroSecond, Multiplier::default()), None);
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_with_empty_id_then_not_added() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &[""], Some(Multiplier(2, 0))));
        assert!(custom.is_empty());
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(
            Second,
            &["sec"],
            Some(Multiplier(2, 0)),
        ));
        assert!(!custom.is_empty());
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                3,
                3,
                Second,
                Multiplier(2, 0),
                vec!["sec"]
            ))
        );
        assert_eq!(custom.get("sec"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_multiple_custom_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(
            Second,
            &["sec"],
            Some(Multiplier(1, 0)),
        ));
        custom.add_custom_time_unit(CustomTimeUnit::new(
            Second,
            &["secs"],
            Some(Multiplier(2, 0)),
        ));
        assert_eq!(
            custom.lookup(Second, Multiplier::default()),
            Some(&make_lookup_result(
                3,
                3,
                Second,
                Multiplier::default(),
                vec!["sec"]
            ))
        );
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                4,
                4,
                Second,
                Multiplier(2, 0),
                vec!["secs"]
            ))
        );
        assert_eq!(custom.get("sec"), Some((Second, Multiplier(1, 0))));
        assert_eq!(custom.get("secs"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_normal_time_unit_already_exists() {
        let mut custom = CustomTimeUnits::with_time_units(&[(Second, &["s"])]);
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &["ss"], Some(Multiplier(2, 0))));
        assert_eq!(
            custom.lookup(Second, Multiplier::default()),
            Some(&make_lookup_result(
                1,
                1,
                Second,
                Multiplier::default(),
                vec!["s"]
            ))
        );
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                2,
                2,
                Second,
                Multiplier(2, 0),
                vec!["ss"]
            ))
        );
        assert_eq!(custom.get("s"), Some((Second, Multiplier(1, 0))));
        assert_eq!(custom.get("ss"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_normal_time_unit_with_same_id() {
        let mut custom = CustomTimeUnits::with_time_units(&[(Second, &["s"])]);
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &["s"], Some(Multiplier(2, 0))));
        assert_eq!(
            custom.lookup(Second, Multiplier::default()),
            Some(&make_lookup_result(
                1,
                1,
                Second,
                Multiplier::default(),
                vec!["s"]
            ))
        );
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                1,
                1,
                Second,
                Multiplier(2, 0),
                vec!["s"]
            ))
        );
        assert_eq!(custom.get("s"), Some((Second, Multiplier(1, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_identifiers_is_empty() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &[], Some(Multiplier(2, 0))));
        assert!(custom.is_empty());
        assert_eq!(custom.lookup(Second, Multiplier(2, 0)), None);
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_adding_same_unit_twice() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &["s"], Some(Multiplier(2, 0))));
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &["s"], Some(Multiplier(2, 0))));
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                1,
                1,
                Second,
                Multiplier(2, 0),
                vec!["s", "s"]
            ))
        );
    }

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
        assert_eq!(parser.parse("1.0"), Ok(Duration::new(1, 0)));
    }

    #[test]
    fn test_custom_duration_parser_init_default() {
        let parser = CustomDurationParser::default();
        assert!(parser.time_units.is_empty());
    }

    #[test]
    fn test_custom_duration_parser_when_add_custom_time_units() {
        let mut parser = CustomDurationParser::new();
        parser.custom_time_unit(CustomTimeUnit::new(
            Year,
            &["century", "centuries"],
            Some(Multiplier(100, 0)),
        ));
        assert_eq!(
            parser.time_units.lookup(Year, Multiplier(100, 0)),
            Some(&make_lookup_result(
                7,
                9,
                Year,
                Multiplier(100, 0),
                vec!["century", "centuries"]
            ))
        );
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
        parser.allow_spaces(true);
        assert!(parser.inner.config.allow_spaces);
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
    fn test_custom_duration_parser_setting_number_is_optional() {
        let mut parser = CustomDurationParser::new();
        parser.number_is_optional(true);
        assert!(parser.inner.config.number_is_optional);
    }

    #[cfg(feature = "negative")]
    #[test]
    fn test_custom_duration_parser_parse_negative_calls_parser() {
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
}
