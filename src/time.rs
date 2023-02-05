// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

/// The time units the parser can understand
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
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
#[derive(Debug, PartialEq)]
pub struct TimeUnits {
    max_length: usize,
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
    /// Create an empty set of [`TimeUnit`]s.
    pub fn new() -> Self {
        Self {
            max_length: Default::default(),
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
    pub fn with_default_time_units() -> Self {
        Self::default()
    }

    /// Create [`TimeUnits`] with a custom set of [`TimeUnit`]s.
    pub fn with_time_units(units: &[TimeUnit]) -> Self {
        let mut time_units = Self::new();
        time_units.add_time_units(units);
        time_units
    }

    /// Create [`TimeUnits`] with a all available [`TimeUnit`]s.
    pub fn with_all_time_units() -> Self {
        Self {
            max_length: DEFAULT_ID_MAX_LENGTH,
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
    pub fn add_time_unit(&mut self, unit: TimeUnit) {
        // TODO match only if the time unit is not already set
        let id = match unit {
            TimeUnit::NanoSecond => {
                let id = DEFAULT_ID_NANO_SECOND;
                self.nanos = Some(id);
                id
            }
            TimeUnit::MicroSecond => {
                let id = DEFAULT_ID_MICRO_SECOND;
                self.micros = Some(id);
                id
            }
            TimeUnit::MilliSecond => {
                let id = DEFAULT_ID_MILLI_SECOND;
                self.millis = Some(id);
                id
            }
            TimeUnit::Second => {
                let id = DEFAULT_ID_SECOND;
                self.seconds = Some(id);
                id
            }
            TimeUnit::Minute => {
                let id = DEFAULT_ID_MINUTE;
                self.minutes = Some(id);
                id
            }
            TimeUnit::Hour => {
                let id = DEFAULT_ID_HOUR;
                self.hours = Some(id);
                id
            }
            TimeUnit::Day => {
                let id = DEFAULT_ID_DAY;
                self.days = Some(id);
                id
            }
            TimeUnit::Week => {
                let id = DEFAULT_ID_WEEK;
                self.weeks = Some(id);
                id
            }
            TimeUnit::Month => {
                let id = DEFAULT_ID_MONTH;
                self.months = Some(id);
                id
            }
            TimeUnit::Year => {
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
    pub fn add_time_units(&mut self, units: &[TimeUnit]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    /// Return `true` if this set of time units is empty.
    pub fn is_empty(&self) -> bool {
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

    /// Return the maximum length in bytes of the identifier in the current set of [`TimeUnit`].
    pub fn max_length(&self) -> usize {
        self.max_length
    }

    /// Return the [`TimeUnit`] associated with the provided `identifier`.
    ///
    /// Returns `None` if no [`TimeUnit`] with the provided `identifier` is present in the current
    /// set of time units.
    pub fn get(&self, identifier: &str) -> Option<TimeUnit> {
        use TimeUnit::*;
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
}
