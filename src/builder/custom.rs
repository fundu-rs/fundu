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

    fn with_default_time_units() -> Self {
        // TODO: use vec![] instead
        let capacity = 1;
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

    fn with_time_units(units: &[IdentifiersSlice<'a>]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

    fn with_all_time_units() -> Self {
        // TODO: use vec![] with capacity 1 instead
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

    fn add_time_unit(&mut self, unit: IdentifiersSlice<'a>) {
        let (time_unit, ids) = unit;
        self.time_units[Self::map_time_unit_to_index(time_unit)]
            .1
            .extend(ids.iter());
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

pub struct CustomDurationParser<'a> {
    time_units: CustomTimeUnits<'a>,
    default_unit: TimeUnit,
}

impl<'a> CustomDurationParser<'a> {
    pub fn new() -> Self {
        Self {
            time_units: CustomTimeUnits::new(),
            default_unit: Default::default(),
        }
    }

    pub fn with_default_time_units() -> Self {
        Self {
            time_units: CustomTimeUnits::with_default_time_units(),
            default_unit: Default::default(),
        }
    }

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
    pub fn time_unit(&mut self, unit: IdentifiersSlice<'a>) -> &mut Self {
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
    /// use fundu::{DurationParser, TimeUnit::*};
    /// use std::time::Duration;
    ///
    /// assert_eq!(
    ///     DurationParser::new().parse("1.2e-1s").unwrap(),
    ///     Duration::new(0, 120_000_000),
    /// );
    /// ```
    #[inline(never)]
    pub fn parse(&mut self, source: &str) -> Result<Duration, ParseError> {
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

    #[test]
    fn test_custom_time_units() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((NanoSecond, &["ns"]));
        assert_eq!(custom.get("ns"), Some(NanoSecond));
    }
}
