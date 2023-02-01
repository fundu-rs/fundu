// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

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
