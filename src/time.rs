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

    /// Return the base [`Multiplier`] of this [`TimeUnit`].
    ///
    /// This multiplier is always seconds based so for example:
    ///
    /// ```ignore
    /// NanoSecond: Multiplier(1, -9)
    /// Second: Multiplier(1, 0)
    /// Year: Multiplier(31557600, 0)
    /// ```
    pub const fn multiplier(&self) -> Multiplier {
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

/// The multiplier of a [`TimeUnit`].
///
/// The multiplier consists of two numbers `(m, e)` which are applied to another number `x` as
/// follows:
///
/// `x * m * 10 ^ e`
///
/// Examples:
///
/// ```ignore
/// let nano_second = Multiplier(1, -9);
/// let second = Multiplier(1, 0);
/// let hour = Multiplier(3600, 0);
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Multiplier(pub u64, pub i16);

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

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Duration {
    is_negative: bool,
    inner: std::time::Duration,
}

impl Duration {
    pub(crate) fn new(is_negative: bool, inner: std::time::Duration) -> Self {
        Self { is_negative, inner }
    }

    #[cfg(feature = "negative")]
    pub(crate) fn saturating_into(&self) -> time::Duration {
        time::Duration::try_from(self).unwrap_or_else(|error| match error {
            TryFromDurationError::NegativeOverflow => time::Duration::MIN,
            TryFromDurationError::PositiveOverflow => time::Duration::MAX,
            TryFromDurationError::NegativeNumber => unreachable!(), // cov:excl-line
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
        (&duration).try_into()
    }
}

#[cfg(feature = "negative")]
impl TryFrom<&Duration> for time::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: &Duration) -> Result<Self, Self::Error> {
        match (duration.is_negative, duration.inner.as_secs()) {
            (true, secs) if secs > i64::MIN.unsigned_abs() => {
                Err(TryFromDurationError::NegativeOverflow)
            }
            (true, secs) => Ok(time::Duration::new(
                secs.wrapping_neg() as i64,
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

    #[cfg(feature = "negative")]
    #[rstest]
    #[case::positive_zero(Duration::new(false, std::time::Duration::ZERO), time::Duration::ZERO)]
    #[case::negative_zero(Duration::new(true, std::time::Duration::ZERO), time::Duration::ZERO)]
    #[case::positive_one(
        Duration::new(false, std::time::Duration::new(1, 0)),
        time::Duration::new(1, 0)
    )]
    #[case::negative_one(
        Duration::new(true, std::time::Duration::new(1, 0)),
        time::Duration::new(-1, 0)
    )]
    #[case::negative_barely_no_overflow(
        Duration::new(true, std::time::Duration::new(i64::MIN.unsigned_abs(), 999_999_999)),
        time::Duration::MIN
    )]
    #[case::negative_barely_overflow(
        Duration::new(true, std::time::Duration::new(i64::MIN.unsigned_abs() + 1, 0)),
        time::Duration::MIN
    )]
    #[case::negative_max_overflow(
        Duration::new(true, std::time::Duration::new(u64::MAX, 999_999_999)),
        time::Duration::MIN
    )]
    #[case::positive_barely_no_overflow(
        Duration::new(false, std::time::Duration::new(i64::MAX as u64, 999_999_999)),
        time::Duration::MAX
    )]
    #[case::positive_barely_overflow(
        Duration::new(false, std::time::Duration::new(i64::MAX as u64 + 1, 999_999_999)),
        time::Duration::MAX
    )]
    #[case::positive_max_overflow(
        Duration::new(false, std::time::Duration::new(u64::MAX, 999_999_999)),
        time::Duration::MAX
    )]
    fn test_duration_saturating_into(#[case] duration: Duration, #[case] expected: time::Duration) {
        assert_eq!(duration.saturating_into(), expected);
    }

    #[cfg(feature = "negative")]
    #[test]
    fn test_duration_try_from_duration_for_time_duration() {
        let duration = Duration::new(false, std::time::Duration::new(1, 0));
        let time_duration: time::Duration = duration.try_into().unwrap();
        assert_eq!(time_duration, time::Duration::new(1, 0));
    }

    #[rstest]
    #[case::zero(
        std::time::Duration::ZERO,
        Duration::new(false, std::time::Duration::ZERO)
    )]
    #[case::one(
        std::time::Duration::new(1, 0),
        Duration::new(false, std::time::Duration::new(1, 0))
    )]
    #[case::with_nano_seconds(
        std::time::Duration::new(1, 123_456_789),
        Duration::new(false, std::time::Duration::new(1, 123_456_789))
    )]
    #[case::max(
        std::time::Duration::MAX,
        Duration::new(false, std::time::Duration::MAX)
    )]
    fn test_from_std_time_duration_for_duration(
        #[case] std_duration: std::time::Duration,
        #[case] expected: Duration,
    ) {
        assert_eq!(Duration::from(std_duration), expected);
    }

    #[rstest]
    #[case::nano_second(NanoSecond, Multiplier(u64::MAX, i16::MIN + 9))]
    #[case::micro_second(MicroSecond, Multiplier(u64::MAX, i16::MIN + 6))]
    #[case::milli_second(MilliSecond, Multiplier(u64::MAX, i16::MIN + 3))]
    #[case::second(Second, Multiplier(u64::MAX, i16::MIN))]
    #[case::minute(Minute, Multiplier(307_445_734_561_825_860, i16::MIN))]
    #[case::hour(Hour, Multiplier(5_124_095_576_030_431, i16::MIN))]
    #[case::day(Day, Multiplier(213_503_982_334_601, i16::MIN))]
    #[case::week(Week, Multiplier(30_500_568_904_943, i16::MIN))]
    #[case::month(Month, Multiplier(7_014_504_553_087, i16::MIN))]
    #[case::year(Year, Multiplier(584_542_046_090, i16::MIN))]
    fn test_multiplier_multiplication_barely_no_panic(
        #[case] time_unit: TimeUnit,
        #[case] multiplier: Multiplier,
    ) {
        let _ = time_unit.multiplier() * multiplier;
    }

    #[rstest]
    #[case::nano_second(NanoSecond, Multiplier(u64::MAX, i16::MIN + 8))]
    #[case::micro_second(MicroSecond, Multiplier(u64::MAX, i16::MIN + 4))]
    #[case::milli_second(MilliSecond, Multiplier(u64::MAX, i16::MIN + 2))]
    #[case::minute(Minute, Multiplier(307_445_734_561_825_860 + 1, i16::MIN))]
    #[case::hour(Hour, Multiplier(5_124_095_576_030_431 + 1, i16::MIN))]
    #[case::day(Day, Multiplier(213_503_982_334_601 + 1, i16::MIN))]
    #[case::week(Week, Multiplier(30_500_568_904_943 + 1, i16::MIN))]
    #[case::month(Month, Multiplier(7_014_504_553_087 + 1, i16::MIN))]
    #[case::year(Year, Multiplier(584_542_046_090 + 1, i16::MIN))]
    #[should_panic]
    fn test_multiplier_multiplication_then_panic(
        #[case] time_unit: TimeUnit,
        #[case] multiplier: Multiplier,
    ) {
        let _ = time_unit.multiplier() * multiplier;
    }
}
