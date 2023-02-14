// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use TimeUnit::*;

/// The default identifier of [`TimeUnit::NanoSecond`]
pub const DEFAULT_ID_NANO_SECOND: &str = "ns";
/// The default identifier of [`TimeUnit::MicroSecond`]
pub const DEFAULT_ID_MICRO_SECOND: &str = "Ms";
/// The default identifier of [`TimeUnit::MicroSecond`]
pub const DEFAULT_ID_MILLI_SECOND: &str = "ms";
/// The default identifier of [`TimeUnit::Second`]
pub const DEFAULT_ID_SECOND: &str = "s";
/// The default identifier of [`TimeUnit::Minute`]
pub const DEFAULT_ID_MINUTE: &str = "m";
/// The default identifier of [`TimeUnit::Hour`]
pub const DEFAULT_ID_HOUR: &str = "h";
/// The default identifier of [`TimeUnit::Day`]
pub const DEFAULT_ID_DAY: &str = "d";
/// The default identifier of [`TimeUnit::Week`]
pub const DEFAULT_ID_WEEK: &str = "w";
/// The default identifier of [`TimeUnit::Month`]
pub const DEFAULT_ID_MONTH: &str = "M";
/// The default identifier of [`TimeUnit::Year`]
pub const DEFAULT_ID_YEAR: &str = "y";

pub const DEFAULT_ID_MAX_LENGTH: usize = 2;

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

/// The time units the parser can understand and needed to configure the [`DurationParser`].
///
/// # Examples
///
/// ```rust
/// use fundu::{DurationParser, TimeUnit};
/// use std::time::Duration;
///
/// assert_eq!(
///     DurationParser::with_time_units(&[TimeUnit::NanoSecond]).parse("42ns").unwrap(),
///     Duration::new(0, 42)
/// );
/// ```
///
/// [`DurationParser`]: crate::DurationParser
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum TimeUnit {
    /// Represents the lowest possible time unit. The default id is given by [`DEFAULT_ID_NANO_SECOND`] = `ns`
    NanoSecond,
    /// The default id is given by [`DEFAULT_ID_MICRO_SECOND`] = `Ms`
    MicroSecond,
    /// The default id is given by [`DEFAULT_ID_MILLI_SECOND`] = `ms`
    MilliSecond,
    /// The default if no time unit is given. The default id is given by [`DEFAULT_ID_SECOND`] = `s`
    Second,
    /// The default id is given by [`DEFAULT_ID_MINUTE`] = `m`
    Minute,
    /// The default id is given by [`DEFAULT_ID_HOUR`] = `h`
    Hour,
    /// The default id is given by [`DEFAULT_ID_DAY`] = `d`
    Day,
    /// The default id is given by [`DEFAULT_ID_WEEK`] = `w`
    Week,
    /// The default id is given by [`DEFAULT_ID_MONTH`] = `M`
    Month,
    /// Represents the hightest possible time unit. The default id is given by [`DEFAULT_ID_YEAR`] = `y`
    Year,
}

impl Default for TimeUnit {
    fn default() -> Self {
        Second
    }
}

impl TimeUnit {
    /// Return the default identifier
    pub fn default_identifier(&self) -> &'static str {
        match self {
            NanoSecond => DEFAULT_ID_NANO_SECOND,
            MicroSecond => DEFAULT_ID_MICRO_SECOND,
            MilliSecond => DEFAULT_ID_MILLI_SECOND,
            Second => DEFAULT_ID_SECOND,
            Minute => DEFAULT_ID_MINUTE,
            Hour => DEFAULT_ID_HOUR,
            Day => DEFAULT_ID_DAY,
            Week => DEFAULT_ID_WEEK,
            Month => DEFAULT_ID_MONTH,
            Year => DEFAULT_ID_YEAR,
        }
    }

    /// Return the multiplier to convert the number with [`TimeUnit`] to seconds.
    ///
    /// The multipliers change their application depending on whether the [`TimeUnit`] is less than,
    /// equal or greater than `seconds`:
    ///
    /// ```text
    /// t <= s => x(t) * 10^-m
    /// t > s  => x(t) * m
    /// where t = time unit, s = second, x = number in t time units, m = multiplier
    /// ```
    pub(crate) fn multiplier(&self) -> u64 {
        match self {
            NanoSecond => 9,
            MicroSecond => 6,
            MilliSecond => 3,
            Second => 0,
            Minute => 60,
            Hour => 3600,
            Day => 86400,
            Week => 604800,
            Month => 2629800, // Year / 12
            Year => 31557600, // 365.25 days
        }
    }
}

pub trait TimeUnitsLike {
    type Unit;

    fn new() -> Self;
    fn with_default_time_units() -> Self;
    fn with_time_units(units: &[Self::Unit]) -> Self;
    fn with_all_time_units() -> Self;
    fn add_time_unit(&mut self, unit: Self::Unit);
    fn add_time_units(&mut self, units: &[Self::Unit]);
    fn set_default_unit(&mut self, unit: TimeUnit);
    fn is_empty(&self) -> bool;
    fn get(&self, identifier: &str) -> Option<TimeUnit>;
    fn get_time_units(&self) -> Vec<TimeUnit>;
}

/// Interface for [`TimeUnit`]s providing common methods to manipulate the available time units.
#[derive(Debug, PartialEq)]
pub struct TimeUnits {
    max_length: usize,
    /// The default [`TimeUnit`]
    pub default: TimeUnit,
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
            max_length: DEFAULT_ID_MAX_LENGTH,
            default: Default::default(),
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

impl TimeUnits {
    /// Return the maximum length in bytes of the identifier in the current set of [`TimeUnit`].
    #[allow(dead_code)]
    pub fn max_length(&self) -> usize {
        self.max_length
    }
}

impl TimeUnitsLike for TimeUnits {
    type Unit = TimeUnit;

    /// Create an empty set of [`TimeUnit`]s.
    fn new() -> Self {
        Self {
            max_length: Default::default(),
            default: Default::default(),
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

    /// Create [`TimeUnits`] with default [`TimeUnit`]s.
    fn with_default_time_units() -> Self {
        Self::default()
    }

    /// Create [`TimeUnits`] with a custom set of [`TimeUnit`]s.
    fn with_time_units(units: &[TimeUnit]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

    /// Create [`TimeUnits`] with a all available [`TimeUnit`]s.
    fn with_all_time_units() -> Self {
        Self {
            max_length: DEFAULT_ID_MAX_LENGTH,
            default: Default::default(),
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
        let id = match unit {
            NanoSecond => {
                let id = DEFAULT_ID_NANO_SECOND;
                self.nanos = Some(id);
                id
            }
            MicroSecond => {
                let id = DEFAULT_ID_MICRO_SECOND;
                self.micros = Some(id);
                id
            }
            MilliSecond => {
                let id = DEFAULT_ID_MILLI_SECOND;
                self.millis = Some(id);
                id
            }
            Second => {
                let id = DEFAULT_ID_SECOND;
                self.seconds = Some(id);
                id
            }
            Minute => {
                let id = DEFAULT_ID_MINUTE;
                self.minutes = Some(id);
                id
            }
            Hour => {
                let id = DEFAULT_ID_HOUR;
                self.hours = Some(id);
                id
            }
            Day => {
                let id = DEFAULT_ID_DAY;
                self.days = Some(id);
                id
            }
            Week => {
                let id = DEFAULT_ID_WEEK;
                self.weeks = Some(id);
                id
            }
            Month => {
                let id = DEFAULT_ID_MONTH;
                self.months = Some(id);
                id
            }
            Year => {
                let id = DEFAULT_ID_YEAR;
                self.years = Some(id);
                id
            }
        };

        let length = id.len();
        if self.max_length < length {
            self.max_length = length;
        }
    }

    /// Add multiple [`TimeUnit`] to the set of already present time units.
    fn add_time_units(&mut self, units: &[TimeUnit]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    /// Set the default [`TimeUnit`]
    fn set_default_unit(&mut self, unit: TimeUnit) {
        self.default = unit;
    }

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
        let id = Some(identifier);
        if id == self.nanos {
            Some(NanoSecond)
        } else if id == self.micros {
            Some(MicroSecond)
        } else if id == self.millis {
            Some(MilliSecond)
        } else if id == self.seconds {
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

    /// Return all [`TimeUnit`]s from the set of active time units ordered.
    #[allow(dead_code)]
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

#[derive(Debug)]
pub struct CustomTimeUnits<'a> {
    default: TimeUnit,
    time_units: [(TimeUnit, Vec<&'a str>); 10],
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

impl<'a> TimeUnitsLike for CustomTimeUnits<'a> {
    type Unit = (TimeUnit, &'a [&'a str]);

    fn new() -> Self {
        let capacity = 5;
        Self {
            default: Default::default(),
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

    fn with_default_time_units() -> Self {
        let capacity = 5;
        let mut nanos = Vec::with_capacity(capacity);
        nanos.push(DEFAULT_ID_NANO_SECOND);
        let mut micros = Vec::with_capacity(capacity);
        micros.push(DEFAULT_ID_MICRO_SECOND);
        let mut millis = Vec::with_capacity(capacity);
        millis.push(DEFAULT_ID_MILLI_SECOND);
        let mut seconds = Vec::with_capacity(capacity);
        seconds.push(DEFAULT_ID_SECOND);
        let mut minutes = Vec::with_capacity(capacity);
        minutes.push(DEFAULT_ID_MINUTE);
        let mut hours = Vec::with_capacity(capacity);
        hours.push(DEFAULT_ID_HOUR);
        let mut days = Vec::with_capacity(capacity);
        days.push(DEFAULT_ID_DAY);
        let mut weeks = Vec::with_capacity(capacity);
        weeks.push(DEFAULT_ID_WEEK);
        let months = Vec::with_capacity(capacity);
        let years = Vec::with_capacity(capacity);
        Self {
            default: Default::default(),
            time_units: [
                (NanoSecond, nanos),
                (MicroSecond, micros),
                (MilliSecond, millis),
                (Second, seconds),
                (Minute, minutes),
                (Hour, hours),
                (Day, days),
                (Week, weeks),
                (Month, months),
                (Year, years),
            ],
        }
    }

    fn with_time_units(units: &[Self::Unit]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

    fn with_all_time_units() -> Self {
        let capacity = 5;
        let mut nanos = Vec::with_capacity(capacity);
        nanos.push(DEFAULT_ID_NANO_SECOND);
        let mut micros = Vec::with_capacity(capacity);
        micros.push(DEFAULT_ID_MICRO_SECOND);
        let mut millis = Vec::with_capacity(capacity);
        millis.push(DEFAULT_ID_MILLI_SECOND);
        let mut seconds = Vec::with_capacity(capacity);
        seconds.push(DEFAULT_ID_SECOND);
        let mut minutes = Vec::with_capacity(capacity);
        minutes.push(DEFAULT_ID_MINUTE);
        let mut hours = Vec::with_capacity(capacity);
        hours.push(DEFAULT_ID_HOUR);
        let mut days = Vec::with_capacity(capacity);
        days.push(DEFAULT_ID_DAY);
        let mut weeks = Vec::with_capacity(capacity);
        weeks.push(DEFAULT_ID_WEEK);
        let mut months = Vec::with_capacity(capacity);
        months.push(DEFAULT_ID_MONTH);
        let mut years = Vec::with_capacity(capacity);
        years.push(DEFAULT_ID_YEAR);
        Self {
            default: Default::default(),
            time_units: [
                (NanoSecond, nanos),
                (MicroSecond, micros),
                (MilliSecond, millis),
                (Second, seconds),
                (Minute, minutes),
                (Hour, hours),
                (Day, days),
                (Week, weeks),
                (Month, months),
                (Year, years),
            ],
        }
    }

    fn add_time_unit(&mut self, unit: Self::Unit) {
        let (time_unit, ids) = unit;
        self.time_units[Self::map_time_unit_to_index(time_unit)]
            .1
            .extend(ids.iter());
    }

    fn add_time_units(&mut self, units: &[Self::Unit]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    fn set_default_unit(&mut self, unit: TimeUnit) {
        self.default = unit;
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
    fn test_time_unit_default_identifier(#[case] time_unit: TimeUnit, #[case] expected: &str) {
        assert_eq!(time_unit.default_identifier(), expected);
    }

    #[rstest]
    #[case::nano_second(NanoSecond, 9)]
    #[case::micro_second(MicroSecond, 6)]
    #[case::milli_second(MilliSecond, 3)]
    #[case::second(Second, 0)]
    #[case::minute(Minute, 60)]
    #[case::hour(Hour, 60 * 60)]
    #[case::day(Day, 60 * 60 * 24)]
    #[case::week(Week, 60 * 60 * 24 * 7)]
    #[case::month(Month, (60 * 60 * 24 * 365 + 60 * 60 * 24 / 4) / 12)] // (365 days + day/4) / 12
    #[case::year(Year, 60 * 60 * 24 * 365 + 60 * 60 * 24 / 4)] // 365 days + day/4
    fn test_time_unit_multiplier(#[case] time_unit: TimeUnit, #[case] expected: u64) {
        assert_eq!(time_unit.multiplier(), expected);
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
    #[case::nano_second(NanoSecond, Some("ns"), 2)]
    #[case::nano_second(MicroSecond, Some("Ms"), 2)]
    #[case::nano_second(MilliSecond, Some("ms"), 2)]
    #[case::nano_second(Second, Some("s"), 1)]
    #[case::nano_second(Minute, Some("m"), 1)]
    #[case::nano_second(Hour, Some("h"), 1)]
    #[case::nano_second(Day, Some("d"), 1)]
    #[case::nano_second(Week, Some("w"), 1)]
    #[case::nano_second(Month, Some("M"), 1)]
    #[case::nano_second(Year, Some("y"), 1)]
    fn test_time_units_add_time_unit(
        #[case] time_unit: TimeUnit,
        #[case] expected: Option<&str>,
        #[case] max_length: usize,
    ) {
        let mut time_units = TimeUnits::new();
        time_units.add_time_unit(time_unit);
        assert_time_unit(&time_units, time_unit, expected);
        assert_eq!(time_units.max_length(), max_length);
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

    #[rstest]
    #[case::default(TimeUnits::default())]
    #[case::new(TimeUnits::new())]
    #[case::with_all_time_units(TimeUnits::with_all_time_units())]
    #[case::with_default_time_units(TimeUnits::with_default_time_units())]
    #[case::with_time_units(TimeUnits::with_time_units(&[NanoSecond]))]
    fn test_time_units_constructors_set_default_time_unit_to_second(#[case] time_units: TimeUnits) {
        assert_eq!(time_units.default, Second);
    }

    #[test]
    fn test_time_units_set_default_time_unit() {
        let mut time_units = TimeUnits::new();
        time_units.set_default_unit(NanoSecond);
        assert_eq!(time_units.default, NanoSecond);
    }

    #[test]
    fn test_custom_time_units() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((NanoSecond, &["ns"]));
        assert_eq!(custom.get("ns"), Some(NanoSecond));
    }
}
