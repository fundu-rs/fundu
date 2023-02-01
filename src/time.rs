// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::collections::HashMap;

// TODO: Add Eq
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
            Month => 2592000,
            Year => 31536000,
        }
    }
}

#[derive(Debug, Default)]
pub struct TimeUnits<'a> {
    time_units: HashMap<&'a str, TimeUnit>,
    max_length: usize,
}

impl<'a> TimeUnits<'a> {
    pub fn new() -> Self {
        Self::default()
    }

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

    pub fn with_time_units(units: &[TimeUnit]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

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

    pub fn add_time_unit(&mut self, unit: TimeUnit) {
        let id = unit.default_identifier();
        let length = id.len();
        self.time_units.insert(id, unit);
        if self.max_length < length {
            self.max_length = length;
        }
    }

    pub fn add_time_units(&mut self, units: &[TimeUnit]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    pub fn is_empty(&self) -> bool {
        self.time_units.is_empty()
    }

    pub fn max_length(&self) -> usize {
        self.max_length
    }

    pub fn get(&self, identifier: &str) -> Option<TimeUnit> {
        self.time_units.get(identifier).cloned()
    }
}
