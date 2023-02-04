// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::collections::HashMap;

// TODO: Add Eq
/// The time units the parser can understand
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum TimeUnit {
    NanoSecond,
    MicroSecond,
    MilliSecond,
    Second,
    Minute,
    Hour,
    Day,
    Week,
    Month,
    Year,
}

impl Default for TimeUnit {
    fn default() -> Self {
        TimeUnit::Second
    }
}

pub const DEFAULT_ID_NANO_SECOND: &str = "ns";
pub const DEFAULT_ID_MICRO_SECOND: &str = "Ms";
pub const DEFAULT_ID_MILLI_SECOND: &str = "ms";
pub const DEFAULT_ID_SECOND: &str = "s";
pub const DEFAULT_ID_MINUTE: &str = "m";
pub const DEFAULT_ID_HOUR: &str = "h";
pub const DEFAULT_ID_DAY: &str = "d";
pub const DEFAULT_ID_WEEK: &str = "w";
pub const DEFAULT_ID_MONTH: &str = "M";
pub const DEFAULT_ID_YEAR: &str = "y";
pub const DEFAULT_ID_MAX_LENGTH: usize = 2;

impl TimeUnit {
    /// Return the default identifier
    pub fn default_identifier(&self) -> &'static str {
        match self {
            TimeUnit::NanoSecond => DEFAULT_ID_NANO_SECOND,
            TimeUnit::MicroSecond => DEFAULT_ID_MICRO_SECOND,
            TimeUnit::MilliSecond => DEFAULT_ID_MILLI_SECOND,
            TimeUnit::Second => DEFAULT_ID_SECOND,
            TimeUnit::Minute => DEFAULT_ID_MINUTE,
            TimeUnit::Hour => DEFAULT_ID_HOUR,
            TimeUnit::Day => DEFAULT_ID_DAY,
            TimeUnit::Week => DEFAULT_ID_WEEK,
            TimeUnit::Month => DEFAULT_ID_MONTH,
            TimeUnit::Year => DEFAULT_ID_YEAR,
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
    pub fn multiplier(&self) -> u64 {
        use TimeUnit::*;

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

/// Interface for [`TimeUnit`]s providing common methods to manipulate the available time units.
#[derive(Debug, Default)]
pub struct TimeUnits<'a> {
    time_units: HashMap<&'a str, TimeUnit>,
    max_length: usize,
}

impl<'a> TimeUnits<'a> {
    /// Create an empty set of [`TimeUnit`]s.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create [`TimeUnits`] with default [`TimeUnit`]s.
    pub fn with_default_time_units() -> Self {
        let mut time_units = HashMap::new();
        time_units.insert(DEFAULT_ID_NANO_SECOND, TimeUnit::NanoSecond);
        time_units.insert(DEFAULT_ID_MICRO_SECOND, TimeUnit::MicroSecond);
        time_units.insert(DEFAULT_ID_MILLI_SECOND, TimeUnit::MilliSecond);
        time_units.insert(DEFAULT_ID_SECOND, TimeUnit::Second);
        time_units.insert(DEFAULT_ID_MINUTE, TimeUnit::Minute);
        time_units.insert(DEFAULT_ID_HOUR, TimeUnit::Hour);
        time_units.insert(DEFAULT_ID_DAY, TimeUnit::Day);
        time_units.insert(DEFAULT_ID_WEEK, TimeUnit::Week);
        Self {
            time_units,
            max_length: DEFAULT_ID_MAX_LENGTH,
        }
    }

    /// Create [`TimeUnits`] with a custom set of [`TimeUnit`]s.
    pub fn with_time_units(units: &[TimeUnit]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

    /// Create [`TimeUnits`] with a all available [`TimeUnit`]s.
    pub fn with_all_time_units() -> Self {
        let mut time_units = HashMap::new();
        time_units.insert(DEFAULT_ID_NANO_SECOND, TimeUnit::NanoSecond);
        time_units.insert(DEFAULT_ID_MICRO_SECOND, TimeUnit::MicroSecond);
        time_units.insert(DEFAULT_ID_MILLI_SECOND, TimeUnit::MilliSecond);
        time_units.insert(DEFAULT_ID_SECOND, TimeUnit::Second);
        time_units.insert(DEFAULT_ID_MINUTE, TimeUnit::Minute);
        time_units.insert(DEFAULT_ID_HOUR, TimeUnit::Hour);
        time_units.insert(DEFAULT_ID_DAY, TimeUnit::Day);
        time_units.insert(DEFAULT_ID_WEEK, TimeUnit::Week);
        time_units.insert(DEFAULT_ID_MONTH, TimeUnit::Month);
        time_units.insert(DEFAULT_ID_YEAR, TimeUnit::Year);
        Self {
            time_units,
            max_length: DEFAULT_ID_MAX_LENGTH,
        }
    }

    /// Add a [`TimeUnit`] to the set of already present time units.
    pub fn add_time_unit(&mut self, unit: TimeUnit) {
        let id = unit.default_identifier();
        let length = id.len();
        self.time_units.insert(id, unit);
        if self.max_length < length {
            self.max_length = length;
        }
    }

    /// Add multiple [`TimeUnit`] to the set of already present time units.
    pub fn add_time_units(&mut self, units: &[TimeUnit]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    /// Return `true` if this set of time units is empty.
    pub fn is_empty(&self) -> bool {
        self.time_units.is_empty()
    }

    /// Return the maximum length in bytes of the identifier in the current set of [`TimeUnit`].
    pub fn max_length(&self) -> usize {
        self.max_length
    }

    /// Return the [`TimeUnit`] associated with the provided `identifier`.
    ///
    /// Returns `None` if no [`TimeUnit`] with the provided `identifier` is present in the current
    /// set of time units.
    pub fn get(&self, identifier: &str) -> Option<TimeUnit> {
        self.time_units.get(identifier).cloned()
    }
}
