// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign};

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
/// use fundu::{Duration, DurationParser, TimeUnit};
///
/// assert_eq!(
///     DurationParser::with_time_units(&[TimeUnit::NanoSecond])
///         .parse("42ns")
///         .unwrap(),
///     Duration::positive(0, 42)
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
        const MULTIPLIERS: [Multiplier; 10] = [
            Multiplier(1, -9),
            Multiplier(1, -6),
            Multiplier(1, -3),
            Multiplier(1, 0),
            Multiplier(60, 0),
            Multiplier(3600, 0),
            Multiplier(86400, 0),
            Multiplier(604800, 0),
            Multiplier(2629800, 0),  // Year / 12
            Multiplier(31557600, 0), // 365.25 days
        ];
        MULTIPLIERS[*self as usize]
    }
}

pub(crate) trait TimeUnitsLike {
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
pub struct Multiplier(pub i64, pub i16);

impl Default for Multiplier {
    fn default() -> Self {
        Self(1, 0)
    }
}

impl Multiplier {
    pub fn coefficient(&self) -> i64 {
        self.0
    }

    pub fn exponent(&self) -> i16 {
        self.1
    }

    pub fn is_negative(&self) -> bool {
        self.0.is_negative()
    }
}

impl Mul for Multiplier {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Multiplier(
            self.0
                .checked_mul(rhs.0)
                .expect("Multiplier: Overflow when multiplying coefficient"),
            self.1
                .checked_add(rhs.1)
                .expect("Multiplier: Overflow when adding exponent"),
        )
    }
}

impl Neg for Multiplier {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Multiplier(self.0.saturating_neg(), self.1)
    }
}

pub trait SaturatingInto<T>: Sized {
    fn saturating_into(self) -> T;
}

#[derive(Debug, Eq, Clone, Copy, Default)]
pub struct Duration {
    is_negative: bool,
    inner: std::time::Duration,
}

impl Duration {
    pub const ZERO: Self = Self {
        is_negative: false,
        inner: std::time::Duration::ZERO,
    };

    pub const MIN: Self = Self {
        is_negative: true,
        inner: std::time::Duration::MAX,
    };

    pub const MAX: Self = Self {
        is_negative: false,
        inner: std::time::Duration::MAX,
    };

    // TODO: If inner is zero then return a positive zero duration ??
    pub fn from_std(is_negative: bool, inner: std::time::Duration) -> Self {
        Self { is_negative, inner }
    }

    // TODO: Remove ??
    pub fn new(is_negative: bool, secs: u64, nanos: u32) -> Self {
        Self {
            is_negative,
            inner: std::time::Duration::new(secs, nanos),
        }
    }

    pub fn positive(secs: u64, nanos: u32) -> Self {
        Self {
            is_negative: false,
            inner: std::time::Duration::new(secs, nanos),
        }
    }

    pub fn negative(secs: u64, nanos: u32) -> Self {
        Self {
            is_negative: true,
            inner: std::time::Duration::new(secs, nanos),
        }
    }

    pub fn is_negative(&self) -> bool {
        self.is_negative
    }

    pub fn is_positive(&self) -> bool {
        !self.is_negative
    }

    pub fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    pub fn abs(&self) -> Self {
        Self::from_std(false, self.inner)
    }

    pub fn checked_add(&self, other: Self) -> Option<Self> {
        match (
            self.is_negative,
            other.is_negative,
            self.inner.cmp(&other.inner),
        ) {
            (true, true, _) => self
                .inner
                .checked_add(other.inner)
                .map(|d| Self::from_std(true, d)),
            (true, false, Ordering::Equal) | (false, true, Ordering::Equal) => Some(Self::ZERO),
            (true, false, Ordering::Greater) => {
                Some(Self::from_std(true, self.inner.sub(other.inner)))
            }
            (true, false, Ordering::Less) => {
                Some(Self::from_std(false, other.inner.sub(self.inner)))
            }
            (false, true, Ordering::Greater) => {
                Some(Self::from_std(false, self.inner.sub(other.inner)))
            }
            (false, true, Ordering::Less) => {
                Some(Self::from_std(true, other.inner.sub(self.inner)))
            }
            (false, false, _) => self
                .inner
                .checked_add(other.inner)
                .map(|d| Self::from_std(false, d)),
        }
    }

    pub fn checked_sub(&self, other: Self) -> Option<Self> {
        self.checked_add(other.neg())
    }

    pub fn saturating_add(&self, other: Self) -> Self {
        match self.checked_add(other) {
            Some(d) => d,
            // checked_add only returns None if both durations are either negative or positive so it
            // is enough to check one of the durations for negativity
            None if self.is_negative => Self::MIN,
            None => Self::MAX,
        }
    }

    pub fn saturating_sub(&self, other: Self) -> Self {
        self.saturating_add(other.neg())
    }
}

impl Add for Duration {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        self.checked_add(rhs)
            .expect("Overflow when adding duration")
    }
}

impl AddAssign for Duration {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs
    }
}

impl Sub for Duration {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self.checked_sub(rhs)
            .expect("Overflow when subtracting duration")
    }
}

impl SubAssign for Duration {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs
    }
}

impl Neg for Duration {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            is_negative: self.is_negative ^ true,
            inner: self.inner,
        }
    }
}

impl PartialEq for Duration {
    fn eq(&self, other: &Self) -> bool {
        (self.is_zero() && other.is_zero())
            || (self.is_negative == other.is_negative && self.inner == other.inner)
    }
}

impl Hash for Duration {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if self.is_zero() {
            false.hash(state);
            self.inner.hash(state);
        } else {
            self.is_negative.hash(state);
            self.inner.hash(state);
        }
    }
}

impl PartialOrd for Duration {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Duration {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.is_negative, other.is_negative) {
            (true, true) => other.inner.cmp(&self.inner),
            (true, false) | (false, true) if self.is_zero() && other.is_zero() => Ordering::Equal,
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => self.inner.cmp(&other.inner),
        }
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

#[cfg(feature = "time")]
impl From<time::Duration> for Duration {
    fn from(duration: time::Duration) -> Self {
        Self {
            is_negative: duration.is_negative(),
            inner: std::time::Duration::new(
                duration.whole_seconds().unsigned_abs(),
                duration.subsec_nanoseconds().unsigned_abs(),
            ),
        }
    }
}

#[cfg(feature = "time")]
impl TryFrom<Duration> for time::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        (&duration).try_into()
    }
}

#[cfg(feature = "time")]
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

#[cfg(feature = "time")]
impl SaturatingInto<time::Duration> for Duration {
    fn saturating_into(self) -> time::Duration {
        match self.try_into() {
            Ok(duration) => duration,
            Err(TryFromDurationError::NegativeOverflow) => time::Duration::MIN,
            Err(TryFromDurationError::PositiveOverflow) => time::Duration::MAX,
            Err(_) => unreachable!(), // cov:excl-line
        }
    }
}

#[cfg(feature = "chrono")]
impl TryFrom<Duration> for chrono::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        (&duration).try_into()
    }
}

#[cfg(feature = "chrono")]
impl TryFrom<&Duration> for chrono::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: &Duration) -> Result<Self, Self::Error> {
        const MAX: chrono::Duration = chrono::Duration::max_value();
        const MIN: chrono::Duration = chrono::Duration::min_value();

        match (duration.is_negative, duration.inner.as_secs()) {
            (true, secs) if secs > MIN.num_seconds().unsigned_abs() => {
                Err(TryFromDurationError::NegativeOverflow)
            }
            (true, secs) => {
                let nanos =
                    chrono::Duration::nanoseconds((duration.inner.subsec_nanos() as i64).neg());
                match chrono::Duration::seconds((secs as i64).neg()).checked_add(&nanos) {
                    Some(d) => Ok(d),
                    None => Err(TryFromDurationError::NegativeOverflow),
                }
            }
            (false, secs) if secs > MAX.num_seconds() as u64 => {
                Err(TryFromDurationError::PositiveOverflow)
            }
            (false, secs) => {
                let nanos = chrono::Duration::nanoseconds(duration.inner.subsec_nanos() as i64);
                match chrono::Duration::seconds(secs as i64).checked_add(&nanos) {
                    Some(d) => Ok(d),
                    None => Err(TryFromDurationError::PositiveOverflow),
                }
            }
        }
    }
}

#[cfg(feature = "chrono")]
impl SaturatingInto<chrono::Duration> for Duration {
    fn saturating_into(self) -> chrono::Duration {
        match self.try_into() {
            Ok(duration) => duration,
            Err(TryFromDurationError::NegativeOverflow) => chrono::Duration::min_value(),
            Err(TryFromDurationError::PositiveOverflow) => chrono::Duration::max_value(),
            Err(_) => unreachable!(),
        }
    }
}

#[cfg(feature = "chrono")]
impl From<chrono::Duration> for Duration {
    fn from(duration: chrono::Duration) -> Self {
        Self {
            is_negative: duration.num_seconds() < 0,
            inner: duration.abs().to_std().unwrap(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::hash_map::DefaultHasher;
    use std::time::Duration as StdDuration;

    #[cfg(feature = "chrono")]
    use chrono::Duration as ChronoDuration;
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

    #[cfg(feature = "time")]
    #[rstest]
    #[case::positive_zero(Duration::ZERO, time::Duration::ZERO)]
    #[case::negative_zero(Duration::negative(0, 0), time::Duration::ZERO)]
    #[case::positive_one(Duration::positive(1, 0), time::Duration::new(1, 0))]
    #[case::negative_one(Duration::negative(1, 0), time::Duration::new(-1, 0))]
    #[case::negative_barely_no_overflow(
        Duration::negative(i64::MIN.unsigned_abs(), 999_999_999),
        time::Duration::MIN
    )]
    #[case::negative_barely_overflow(
        Duration::negative(i64::MIN.unsigned_abs() + 1, 0),
        time::Duration::MIN
    )]
    #[case::negative_max_overflow(Duration::negative(u64::MAX, 999_999_999), time::Duration::MIN)]
    #[case::positive_barely_no_overflow(
        Duration::positive(i64::MAX as u64, 999_999_999),
        time::Duration::MAX
    )]
    #[case::positive_barely_overflow(
        Duration::positive(i64::MAX as u64 + 1, 999_999_999),
        time::Duration::MAX
    )]
    #[case::positive_max_overflow(Duration::positive(u64::MAX, 999_999_999), time::Duration::MAX)]
    fn test_fundu_duration_saturating_into_time_duration(
        #[case] duration: Duration,
        #[case] expected: time::Duration,
    ) {
        assert_eq!(
            SaturatingInto::<time::Duration>::saturating_into(duration),
            expected
        );
    }

    #[cfg(feature = "time")]
    #[test]
    fn test_duration_try_from_duration_for_time_duration() {
        let duration = Duration::from_std(false, std::time::Duration::new(1, 0));
        let time_duration: time::Duration = duration.try_into().unwrap();
        assert_eq!(time_duration, time::Duration::new(1, 0));
    }

    #[rstest]
    #[case::zero(
        std::time::Duration::ZERO,
        Duration::from_std(false, std::time::Duration::ZERO)
    )]
    #[case::one(
        std::time::Duration::new(1, 0),
        Duration::from_std(false, std::time::Duration::new(1, 0))
    )]
    #[case::with_nano_seconds(
        std::time::Duration::new(1, 123_456_789),
        Duration::from_std(false, std::time::Duration::new(1, 123_456_789))
    )]
    #[case::max(
        std::time::Duration::MAX,
        Duration::from_std(false, std::time::Duration::MAX)
    )]
    fn test_from_std_time_duration_for_duration(
        #[case] std_duration: std::time::Duration,
        #[case] expected: Duration,
    ) {
        assert_eq!(Duration::from(std_duration), expected);
    }

    #[test]
    fn test_multiplier_get_coefficient() {
        let multi = Multiplier(1234, 0);
        assert_eq!(multi.coefficient(), 1234);
    }

    #[test]
    fn test_multiplier_get_exponent() {
        let multi = Multiplier(0, 1234);
        assert_eq!(multi.exponent(), 1234);
    }

    #[rstest]
    #[case::zero(Multiplier(0, 0), false)]
    #[case::negative(Multiplier(-1, 0), true)]
    #[case::positive(Multiplier(1, 0), false)]
    #[case::negative_exponent(Multiplier(1, -1), false)]
    #[case::positive_exponent(Multiplier(-1, 1), true)]
    fn test_multiplier_is_negative(#[case] multi: Multiplier, #[case] expected: bool) {
        assert_eq!(multi.is_negative(), expected);
    }

    #[rstest]
    #[case::nano_second(NanoSecond, Multiplier(i64::MAX, i16::MIN + 9))]
    #[case::micro_second(MicroSecond, Multiplier(i64::MAX, i16::MIN + 6))]
    #[case::milli_second(MilliSecond, Multiplier(i64::MAX, i16::MIN + 3))]
    #[case::second(Second, Multiplier(i64::MAX, i16::MIN))]
    #[case::minute(Minute, Multiplier(i64::MAX / 60, i16::MIN))]
    #[case::hour(Hour, Multiplier(i64::MAX / (60 * 60), i16::MIN))]
    #[case::day(Day, Multiplier(i64::MAX / (60 * 60 * 24), i16::MIN))]
    #[case::week(Week, Multiplier(i64::MAX / (60 * 60 * 24 * 7), i16::MIN))]
    #[case::month(Month, Multiplier(3_507_252_276_543, i16::MIN))]
    #[case::year(Year, Multiplier(292_271_023_045, i16::MIN))]
    fn test_multiplier_multiplication_barely_no_panic(
        #[case] time_unit: TimeUnit,
        #[case] multiplier: Multiplier,
    ) {
        let _ = time_unit.multiplier() * multiplier;
    }

    #[rstest]
    #[case::nano_second(NanoSecond, Multiplier(i64::MAX, i16::MIN + 8))]
    #[case::micro_second(MicroSecond, Multiplier(i64::MAX, i16::MIN + 4))]
    #[case::milli_second(MilliSecond, Multiplier(i64::MAX, i16::MIN + 2))]
    #[case::minute(Minute, Multiplier(i64::MAX / 60 + 1, i16::MIN))]
    #[case::hour(Hour, Multiplier(i64::MAX / (60 * 60) + 1, i16::MIN))]
    #[case::day(Day, Multiplier(i64::MAX / (60 * 60 * 24) + 1, i16::MIN))]
    #[case::week(Week, Multiplier(i64::MAX / (60 * 60 * 24 * 7) + 1, i16::MIN))]
    #[case::month(Month, Multiplier(3_507_252_276_543 + 1, i16::MIN))]
    #[case::year(Year, Multiplier(292_271_023_045 + 1, i16::MIN))]
    #[should_panic]
    fn test_multiplier_multiplication_then_panic(
        #[case] time_unit: TimeUnit,
        #[case] multiplier: Multiplier,
    ) {
        let _ = time_unit.multiplier() * multiplier;
    }

    #[rstest]
    #[case::both_standard_zero(Duration::ZERO, Duration::ZERO, Duration::ZERO)]
    #[case::both_positive_zero(
        Duration::from_std(false, StdDuration::ZERO),
        Duration::from_std(false, StdDuration::ZERO),
        Duration::from_std(false, StdDuration::ZERO)
    )]
    #[case::both_negative_zero(
        Duration::from_std(true, StdDuration::ZERO),
        Duration::from_std(true, StdDuration::ZERO),
        Duration::from_std(true, StdDuration::ZERO)
    )]
    #[case::one_add_zero(
        Duration::from_std(false, StdDuration::new(1, 0)),
        Duration::ZERO,
        Duration::from_std(false, StdDuration::new(1, 0))
    )]
    #[case::minus_one_add_zero(
        Duration::from_std(true, StdDuration::new(1, 0)),
        Duration::ZERO,
        Duration::from_std(true, StdDuration::new(1, 0))
    )]
    #[case::minus_one_add_plus_one(
        Duration::from_std(true, StdDuration::new(1, 0)),
        Duration::from_std(false, StdDuration::new(1, 0)),
        Duration::ZERO
    )]
    #[case::minus_one_add_plus_two_then_carry(
        Duration::from_std(true, StdDuration::new(1, 0)),
        Duration::from_std(false, StdDuration::new(2, 0)),
        Duration::from_std(false, StdDuration::new(1, 0))
    )]
    #[case::minus_one_nano_add_one_then_carry(
        Duration::from_std(true, StdDuration::new(0, 1)),
        Duration::from_std(false, StdDuration::new(1, 0)),
        Duration::from_std(false, StdDuration::new(0, 999_999_999))
    )]
    #[case::plus_one_nano_add_minus_one_then_carry(
        Duration::from_std(false, StdDuration::new(0, 1)),
        Duration::from_std(true, StdDuration::new(1, 0)),
        Duration::from_std(true, StdDuration::new(0, 999_999_999))
    )]
    #[case::plus_one_add_minus_two_then_carry(
        Duration::from_std(false, StdDuration::new(1, 0)),
        Duration::from_std(true, StdDuration::new(2, 0)),
        Duration::from_std(true, StdDuration::new(1, 0))
    )]
    #[case::one_sec_below_min_add_max(
        Duration::from_std(true, StdDuration::new(u64::MAX - 1, 999_999_999)),
        Duration::MAX,
        Duration::from_std(false, StdDuration::new(1, 0)))
    ]
    #[case::one_nano_below_min_add_max(
        Duration::from_std(true, StdDuration::new(u64::MAX, 999_999_998)),
        Duration::MAX,
        Duration::from_std(false, StdDuration::new(0, 1))
    )]
    #[case::one_sec_below_max_add_min(
        Duration::from_std(false, StdDuration::new(u64::MAX - 1, 999_999_999)),
        Duration::MIN,
        Duration::from_std(true, StdDuration::new(1, 0)))
    ]
    #[case::one_nano_below_max_add_min(
        Duration::from_std(false, StdDuration::new(u64::MAX, 999_999_998)),
        Duration::MIN,
        Duration::from_std(true, StdDuration::new(0, 1))
    )]
    #[case::min_and_max(Duration::MIN, Duration::MAX, Duration::ZERO)]
    fn test_fundu_duration_checked_add_then_is_some(
        #[case] lhs: Duration,
        #[case] rhs: Duration,
        #[case] expected: Duration,
    ) {
        assert_eq!(Some(expected), lhs.checked_add(rhs));
        assert_eq!(Some(expected), rhs.checked_add(lhs));
    }

    // TODO: add more tests
    #[rstest]
    #[case::min(Duration::MIN, Duration::MIN)]
    #[case::max(Duration::MAX, Duration::MAX)]
    fn test_fundu_duration_checked_add_then_return_none(
        #[case] lhs: Duration,
        #[case] rhs: Duration,
    ) {
        assert_eq!(None, lhs.checked_add(rhs));
    }

    #[cfg(feature = "chrono")]
    #[rstest]
    #[case::zero(Duration::ZERO, ChronoDuration::zero())]
    #[case::negative_zero(Duration::negative(0, 0), ChronoDuration::zero())]
    #[case::positive_one_sec(Duration::positive(1, 0), ChronoDuration::seconds(1))]
    #[case::positive_one_sec_and_nano(
        Duration::positive(1, 1),
        ChronoDuration::nanoseconds(1_000_000_001)
    )]
    #[case::negative_one_sec(Duration::negative(1, 0), ChronoDuration::seconds(-1))]
    #[case::negative_one_sec_and_nano(
        Duration::negative(1, 1),
        ChronoDuration::nanoseconds(-1_000_000_001)
    )]
    #[case::max_nanos(
        Duration::positive(0, 999_999_999),
        ChronoDuration::nanoseconds(999_999_999)
    )]
    #[case::min_nanos(
        Duration::negative(0, 999_999_999),
        ChronoDuration::nanoseconds(-999_999_999)
    )]
    #[case::max_secs(
        Duration::positive(i64::MAX as u64 / 1000, 0),
        ChronoDuration::seconds(i64::MAX / 1000))
    ]
    #[case::max_secs_and_nanos(
        Duration::positive(i64::MAX as u64 / 1000, 807_000_000),
        ChronoDuration::max_value())
    ]
    #[case::secs_and_nanos_one_below_max(
        Duration::positive(i64::MAX as u64 / 1000, 807_000_000 - 1),
        ChronoDuration::max_value().checked_sub(&ChronoDuration::nanoseconds(1)).unwrap())
    ]
    #[case::min_secs(
        Duration::negative(i64::MIN.unsigned_abs() / 1000, 0),
        ChronoDuration::seconds(i64::MIN / 1000))
    ]
    #[case::min_secs_and_nanos(
        Duration::negative(i64::MIN.unsigned_abs() / 1000, 808_000_000),
        ChronoDuration::min_value())
    ]
    #[case::secs_and_nanos_one_above_min(
        Duration::negative(i64::MIN.unsigned_abs() / 1000, 808_000_000 - 1),
        ChronoDuration::min_value().checked_add(&ChronoDuration::nanoseconds(1)).unwrap())
    ]
    fn test_chrono_try_from_fundu_duration(
        #[case] duration: Duration,
        #[case] expected: ChronoDuration,
    ) {
        let chrono_duration: ChronoDuration = duration.try_into().unwrap();
        assert_eq!(chrono_duration, expected)
    }

    #[cfg(feature = "chrono")]
    #[rstest]
    #[case::positive_overflow_secs(
        Duration::positive(i64::MAX as u64 / 1000 + 1, 0),
        TryFromDurationError::PositiveOverflow)
    ]
    #[case::positive_overflow_secs_and_nanos(
        Duration::positive(i64::MAX as u64 / 1000, 807_000_000 + 1),
        TryFromDurationError::PositiveOverflow)
    ]
    #[case::positive_overflow_max_fundu_duration(
        Duration::MAX,
        TryFromDurationError::PositiveOverflow
    )]
    #[case::negative_overflow_secs(
        Duration::negative(i64::MIN.unsigned_abs() / 1000 + 1, 0),
        TryFromDurationError::NegativeOverflow)
    ]
    #[case::negative_overflow_secs_and_nanos(
        Duration::negative(i64::MIN.unsigned_abs() / 1000, 808_000_001),
        TryFromDurationError::NegativeOverflow)
    ]
    #[case::negative_overflow_min_fundu_duration(
        Duration::MIN,
        TryFromDurationError::NegativeOverflow
    )]
    fn test_chrono_try_from_fundu_duration_then_error(
        #[case] duration: Duration,
        #[case] expected: TryFromDurationError,
    ) {
        let result: Result<ChronoDuration, TryFromDurationError> = duration.try_into();
        assert_eq!(result.unwrap_err(), expected)
    }

    #[rstest]
    #[case::positive_zero(Duration::ZERO, Duration::ZERO, Ordering::Equal)]
    #[case::negative_zero(Duration::negative(0, 0), Duration::negative(0, 0), Ordering::Equal)]
    #[case::negative_zero_and_positive_zero(
        Duration::negative(0, 0),
        Duration::ZERO,
        Ordering::Equal
    )]
    #[case::both_positive_one_sec(
        Duration::positive(1, 0),
        Duration::positive(1, 0),
        Ordering::Equal
    )]
    #[case::both_negative_one_sec(
        Duration::negative(1, 0),
        Duration::negative(1, 0),
        Ordering::Equal
    )]
    #[case::negative_and_positive_one_sec(
        Duration::negative(1, 0),
        Duration::positive(1, 0),
        Ordering::Less
    )]
    #[case::one_nano_second_difference_positive(
        Duration::ZERO,
        Duration::positive(0, 1),
        Ordering::Less
    )]
    #[case::one_nano_second_difference_negative(
        Duration::ZERO,
        Duration::negative(0, 1),
        Ordering::Greater
    )]
    #[case::max(Duration::MAX, Duration::MAX, Ordering::Equal)]
    #[case::one_nano_below_max(
        Duration::MAX,
        Duration::positive(u64::MAX, 999_999_998),
        Ordering::Greater
    )]
    #[case::min(Duration::MIN, Duration::MIN, Ordering::Equal)]
    #[case::one_nano_above_min(
        Duration::MIN,
        Duration::negative(u64::MAX, 999_999_998),
        Ordering::Less
    )]
    #[case::min_max(Duration::MIN, Duration::MAX, Ordering::Less)]
    #[case::mixed_positive(
        Duration::positive(123, 987),
        Duration::positive(987, 123),
        Ordering::Less
    )]
    #[case::mixed_negative(
        Duration::negative(123, 987),
        Duration::negative(987, 123),
        Ordering::Greater
    )]
    #[case::mixed_positive_and_negative(
        Duration::positive(123, 987),
        Duration::negative(987, 123),
        Ordering::Greater
    )]
    fn test_duration_partial_and_total_ordering(
        #[case] lhs: Duration,
        #[case] rhs: Duration,
        #[case] expected: Ordering,
    ) {
        assert_eq!(lhs.partial_cmp(&rhs), Some(expected));
        assert_eq!(rhs.partial_cmp(&lhs), Some(expected.reverse()));
    }

    #[rstest]
    #[case::positive_zero(Duration::ZERO, Duration::ZERO)]
    #[case::negative_zero(Duration::negative(0, 0), Duration::negative(0, 0))]
    #[case::negative_zero_and_positive_zero(Duration::negative(0, 0), Duration::ZERO)]
    #[case::positive_one_sec(Duration::positive(1, 0), Duration::positive(1, 0))]
    #[case::negative_one_sec(Duration::negative(1, 0), Duration::negative(1, 0))]
    #[case::max(Duration::MAX, Duration::MAX)]
    #[case::min(Duration::MIN, Duration::MIN)]
    fn test_duration_hash_and_eq_property_when_equal(
        #[case] duration: Duration,
        #[case] other: Duration,
    ) {
        assert_eq!(duration, other);
        assert_eq!(other, duration);

        let mut hasher = DefaultHasher::new();
        duration.hash(&mut hasher);

        let mut other_hasher = DefaultHasher::new();
        other.hash(&mut other_hasher);

        assert_eq!(hasher.finish(), other_hasher.finish());
    }

    #[rstest]
    #[case::zero_and_positive_one(Duration::ZERO, Duration::positive(1, 0))]
    #[case::zero_and_negative_one(Duration::ZERO, Duration::negative(1, 0))]
    #[case::positive_sec(Duration::positive(1, 0), Duration::negative(2, 0))]
    #[case::positive_and_negative_one_sec(Duration::positive(1, 0), Duration::negative(1, 0))]
    #[case::min_and_max(Duration::MIN, Duration::MAX)]
    fn test_duration_hash_and_eq_property_when_not_equal(
        #[case] duration: Duration,
        #[case] other: Duration,
    ) {
        assert_ne!(duration, other);
        assert_ne!(other, duration);

        let mut hasher = DefaultHasher::new();
        duration.hash(&mut hasher);

        let mut other_hasher = DefaultHasher::new();
        other.hash(&mut other_hasher);

        assert_ne!(hasher.finish(), other_hasher.finish());
    }
}
