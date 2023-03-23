// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use TimeUnit::*;

use crate::error::TryFromDurationError;

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

pub(crate) const DEFAULT_TIME_UNIT: TimeUnit = Second;

/// The time units the parser can understand and needed to configure the [`DurationParser`].
///
/// # Examples
///
/// ```rust
/// use std::time::Duration;
///
/// use fundu::{DurationParser, TimeUnit};
///
/// assert_eq!(
///     DurationParser::with_time_units(&[TimeUnit::NanoSecond])
///         .parse("42ns")
///         .unwrap(),
///     Duration::new(0, 42)
/// );
/// ```
///
/// [`DurationParser`]: crate::DurationParser
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum TimeUnit {
    /// Represents the lowest possible time unit. The default id is given by
    /// [`DEFAULT_ID_NANO_SECOND`] = `ns`
    NanoSecond,
    /// The default id is given by [`DEFAULT_ID_MICRO_SECOND`] = `Ms`
    MicroSecond,
    /// The default id is given by [`DEFAULT_ID_MILLI_SECOND`] = `ms`
    MilliSecond,
    /// The default if no time unit is given. The default id is given by [`DEFAULT_ID_SECOND`] =
    /// `s`
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
    /// Represents the hightest possible time unit. The default id is given by [`DEFAULT_ID_YEAR`]
    /// = `y`
    Year,
}

impl Default for TimeUnit {
    fn default() -> Self {
        DEFAULT_TIME_UNIT
    }
}

impl TimeUnit {
    /// Return the default identifier
    pub const fn default_identifier(&self) -> &'static str {
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

    /// Return the multiplier `(m, e)` to convert a number `x` with [`TimeUnit`] to seconds.
    ///
    /// ```text
    /// x * m * 10 ^ e
    /// where  m = multiplier
    /// ```
    pub(crate) const fn multiplier(&self) -> Multiplier {
        match self {
            NanoSecond => Multiplier(1, -9),
            MicroSecond => Multiplier(1, -6),
            MilliSecond => Multiplier(1, -3),
            Second => Multiplier(1, 0),
            Minute => Multiplier(60, 0),
            Hour => Multiplier(3600, 0),
            Day => Multiplier(86400, 0),
            Week => Multiplier(604800, 0),
            Month => Multiplier(2629800, 0), // Year / 12
            Year => Multiplier(31557600, 0), // 365.25 days
        }
    }
}

pub trait TimeUnitsLike {
    fn is_empty(&self) -> bool;
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)>;
}

/// The multiplier of a TimeUnit to calculate the final [`std::time::Duration`]
///
/// This multiplier consists of two numbers `(m, exp)` which are applied to a number `x` as follows:
/// `x * m * 10 ^ e`
///
/// Examples:
///
/// ```text
/// NanoSecond: (1, -9)
/// Second: (1, 0)
/// Hour: (3600, 0)
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Multiplier(pub u64, pub i32);

impl Default for Multiplier {
    fn default() -> Self {
        Self(1, 0)
    }
}

impl std::ops::Mul for Multiplier {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Multiplier(self.0 * rhs.0, self.1 + rhs.1)
    }
}

pub(crate) struct Duration {
    is_negative: bool,
    inner: std::time::Duration,
}

impl Duration {
    pub(crate) fn new(is_negative: bool, inner: std::time::Duration) -> Self {
        Self { is_negative, inner }
    }

    #[cfg(feature = "negative")]
    pub(crate) fn saturating_into(self) -> time::Duration {
        time::Duration::try_from(self).unwrap_or_else(|error| match error {
            TryFromDurationError::NegativeOverflow => time::Duration::MIN,
            TryFromDurationError::PositiveOverflow => time::Duration::MAX,
            TryFromDurationError::NegativeNumber => unreachable!(),
        })
    }
}

impl From<std::time::Duration> for Duration {
    fn from(duration: std::time::Duration) -> Self {
        Self {
            is_negative: false,
            inner: duration,
        }
    }
}

impl TryFrom<Duration> for std::time::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        if duration.is_negative {
            Err(TryFromDurationError::NegativeNumber)
        } else {
            Ok(duration.inner)
        }
    }
}

#[cfg(feature = "negative")]
impl TryFrom<Duration> for time::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        match (duration.is_negative, duration.inner.as_secs()) {
            (true, secs) if secs > i64::MIN.unsigned_abs() => {
                Err(TryFromDurationError::NegativeOverflow)
            }
            (true, secs) => Ok(time::Duration::new(
                -(secs as i64),
                -(duration.inner.subsec_nanos() as i32),
            )),
            (false, secs) if secs > i64::MAX as u64 => Err(TryFromDurationError::PositiveOverflow),
            (false, secs) => Ok(time::Duration::new(
                secs as i64,
                duration.inner.subsec_nanos() as i32,
            )),
        }
    }
}

#[cfg(feature = "negative")]
#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;

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
    #[case::nano_second(NanoSecond, Multiplier(1, -9))]
    #[case::micro_second(MicroSecond, Multiplier(1, -6))]
    #[case::milli_second(MilliSecond, Multiplier(1, -3))]
    #[case::second(Second, Multiplier(1, 0))]
    #[case::minute(Minute, Multiplier(60, 0))]
    #[case::hour(Hour, Multiplier(60 * 60, 0))]
    #[case::day(Day, Multiplier(60 * 60 * 24, 0))]
    #[case::week(Week, Multiplier(60 * 60 * 24 * 7, 0))]
    #[case::month(Month, Multiplier((60 * 60 * 24 * 365 + 60 * 60 * 24 / 4) / 12, 0))] // (365 days + day/4) / 12
    #[case::year(Year, Multiplier(60 * 60 * 24 * 365 + 60 * 60 * 24 / 4, 0))] // 365 days + day/4
    fn test_time_unit_multiplier(#[case] time_unit: TimeUnit, #[case] expected: Multiplier) {
        assert_eq!(time_unit.multiplier(), expected);
    }
}
