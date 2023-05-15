// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Add, AddAssign, Mul, Neg, Sub, SubAssign};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
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
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Multiplier(pub i64, pub i16);

impl Default for Multiplier {
    fn default() -> Self {
        Self(1, 0)
    }
}

impl Multiplier {
    /// Return the coefficient component of the `Multiplier`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Multiplier;
    ///
    /// let multiplier = Multiplier(123, 45);
    /// assert_eq!(multiplier.coefficient(), 123);
    /// ```
    #[inline]
    pub const fn coefficient(&self) -> i64 {
        self.0
    }

    /// Return the exponent component of the `Multiplier`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Multiplier;
    ///
    /// let multiplier = Multiplier(123, 45);
    /// assert_eq!(multiplier.exponent(), 45);
    /// ```
    #[inline]
    pub const fn exponent(&self) -> i16 {
        self.1
    }

    /// Return true if the `Multiplier` is negative
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Multiplier;
    ///
    /// let multiplier = Multiplier(-123, 45);
    /// assert!(multiplier.is_negative());
    /// ```
    #[inline]
    pub const fn is_negative(&self) -> bool {
        !self.is_positive()
    }

    /// Return true if the `Multiplier` is positive
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Multiplier;
    ///
    /// let multiplier = Multiplier(123, 45);
    /// assert!(multiplier.is_positive());
    /// ```
    #[inline]
    pub const fn is_positive(&self) -> bool {
        self.0 == 0 || self.0.is_positive()
    }

    /// Checked `Multiplier` multiplication. Computes `self * other`, returning `None` if an
    /// overflow occurred.
    ///
    /// Let `a, b` be multipliers, with `m` being the coefficient and `e` the exponent. The
    /// multiplication is performed such that `(x.m, x.e) = (a.m * b.m, a.e + b.e)`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Multiplier;
    ///
    /// assert_eq!(
    ///     Multiplier(1, 2).checked_mul(Multiplier(3, 4)),
    ///     Some(Multiplier(3, 6))
    /// );
    /// assert_eq!(
    ///     Multiplier(-1, 2).checked_mul(Multiplier(3, -4)),
    ///     Some(Multiplier(-3, -2))
    /// );
    /// assert_eq!(Multiplier(2, 0).checked_mul(Multiplier(i64::MAX, 1)), None);
    /// assert_eq!(Multiplier(1, 2).checked_mul(Multiplier(1, i16::MAX)), None);
    /// ```
    #[inline]
    pub const fn checked_mul(&self, rhs: Self) -> Option<Self> {
        if let Some(coefficient) = self.0.checked_mul(rhs.0) {
            if let Some(exponent) = self.1.checked_add(rhs.1) {
                return Some(Multiplier(coefficient, exponent));
            }
        }
        None
    }

    /// Saturating negation. Computes `-self`, returning `i64::MAX` if `self.coefficient() ==
    /// i64::MIN` instead of overflowing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Multiplier;
    ///
    /// assert_eq!(Multiplier(1, 2).saturating_neg(), Multiplier(-1, 2));
    /// assert_eq!(Multiplier(-1, 2).saturating_neg(), Multiplier(1, 2));
    /// assert_eq!(
    ///     Multiplier(i64::MIN, 2).saturating_neg(),
    ///     Multiplier(i64::MAX, 2)
    /// );
    /// ```
    #[inline]
    pub const fn saturating_neg(&self) -> Self {
        Multiplier(self.0.saturating_neg(), self.1)
    }
}

impl Mul for Multiplier {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.checked_mul(rhs)
            .expect("Multiplier: Overflow when multiplying")
    }
}

/// Conversion which saturates at the maximum or maximum instead of overflowing
pub trait SaturatingInto<T>: Sized {
    /// Performs the saturating conversion
    fn saturating_into(self) -> T;
}

/// The duration which is returned by the parser
///
/// The `Duration` of this library implements conversions to a [`std::time::Duration`] and if the
/// feature is activated into a [`time::Duration`] respectively [`chrono::Duration`]. This crates
/// duration is a superset of the aforementioned durations, so converting to fundu's duration with
/// `From` or `Into` is lossless. Converting from [`crate::Duration`] to the other durations can
/// overflow the other duration's value range, but `TryFrom` is implement for all of these
/// durations. Note that fundu's duration also implements [`SaturatingInto`] for the above durations
/// which performs the conversion saturating at the maximum or minimum of these durations.
///
/// # Examples
///
/// Basic conversions from [`Duration`] to [`std::time::Duration`].
///
/// ```rust
/// use std::time::Duration as StdDuration;
///
/// use fundu::{Duration, SaturatingInto, TryFromDurationError};
///
/// let result: Result<StdDuration, TryFromDurationError> = Duration::positive(1, 2).try_into();
/// assert_eq!(result, Ok(StdDuration::new(1, 2)));
///
/// let result: Result<StdDuration, TryFromDurationError> = Duration::negative(1, 2).try_into();
/// assert_eq!(result, Err(TryFromDurationError::NegativeDuration));
///
/// let duration: StdDuration = Duration::negative(1, 2).saturating_into();
/// assert_eq!(duration, StdDuration::ZERO);
///
/// let duration: StdDuration = Duration::MAX.saturating_into();
/// assert_eq!(duration, StdDuration::MAX);
/// ```
#[derive(Debug, Eq, Clone, Copy, Default)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Duration {
    is_negative: bool,
    inner: std::time::Duration,
}

impl Duration {
    /// A duration of zero time
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::ZERO;
    /// assert!(duration.is_zero());
    /// ```
    pub const ZERO: Self = Self {
        is_negative: false,
        inner: std::time::Duration::ZERO,
    };

    /// The minimum duration
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::MIN;
    /// assert_eq!(Duration::negative(u64::MAX, 999_999_999), duration);
    /// ```
    pub const MIN: Self = Self {
        is_negative: true,
        inner: std::time::Duration::MAX,
    };

    /// The maximum duration
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::MAX;
    /// assert_eq!(Duration::positive(u64::MAX, 999_999_999), duration);
    /// ```
    pub const MAX: Self = Self {
        is_negative: false,
        inner: std::time::Duration::MAX,
    };

    /// Creates a new `Duration` from a [`std::time::Duration`] which can be negative or positive
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::from_std(false, std::time::Duration::new(1, 0));
    /// assert_eq!(Duration::positive(1, 0), duration);
    ///
    /// let duration = Duration::from_std(true, std::time::Duration::new(1, 0));
    /// assert_eq!(Duration::negative(1, 0), duration);
    /// ```
    pub const fn from_std(is_negative: bool, inner: std::time::Duration) -> Self {
        Self { is_negative, inner }
    }

    /// Creates a new positive `Duration`
    ///
    /// # Panics
    ///
    /// This constructor will panic if creating a [`std::time::Duration`] with the same parameters
    /// would panic
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::positive(1, 0);
    /// assert!(duration.is_positive());
    ///
    /// let duration = Duration::positive(0, 0);
    /// assert!(duration.is_positive());
    /// ```
    pub const fn positive(secs: u64, nanos: u32) -> Self {
        Self {
            is_negative: false,
            inner: std::time::Duration::new(secs, nanos),
        }
    }

    /// Creates a new negative `Duration`
    ///
    /// # Panics
    ///
    /// This constructor will panic if creating a [`std::time::Duration`] with the same parameters
    /// would panic
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::negative(1, 0);
    /// assert!(duration.is_negative());
    /// ```
    pub const fn negative(secs: u64, nanos: u32) -> Self {
        Self {
            is_negative: true,
            inner: std::time::Duration::new(secs, nanos),
        }
    }

    /// Returns true if the `Duration` is negative
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::MIN;
    /// assert!(duration.is_negative());
    ///
    /// let duration = Duration::negative(0, 1);
    /// assert!(duration.is_negative());
    /// ```
    #[inline]
    pub const fn is_negative(&self) -> bool {
        self.is_negative
    }

    /// Returns true if the `Duration` is positive
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::ZERO;
    /// assert!(duration.is_positive());
    ///
    /// let duration = Duration::positive(0, 1);
    /// assert!(duration.is_positive());
    /// ```
    #[inline]
    pub const fn is_positive(&self) -> bool {
        !self.is_negative
    }

    /// Returns true if the `Duration` is zero
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::ZERO;
    /// assert!(duration.is_zero());
    ///
    /// let duration = Duration::positive(0, 0);
    /// assert!(duration.is_zero());
    ///
    /// let duration = Duration::negative(0, 0);
    /// assert!(duration.is_zero());
    /// ```
    #[inline]
    pub const fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }

    /// Returns the absolute value of the duration
    ///
    /// This operation is lossless.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// let duration = Duration::MIN;
    /// assert_eq!(duration.abs(), Duration::MAX);
    ///
    /// let duration = Duration::negative(1, 0);
    /// assert_eq!(duration.abs(), Duration::positive(1, 0));
    ///
    /// let duration = Duration::positive(1, 0);
    /// assert_eq!(duration.abs(), Duration::positive(1, 0));
    /// ```
    #[inline]
    pub const fn abs(&self) -> Self {
        Self::from_std(false, self.inner)
    }

    /// Sums this duration with the `other` duration, returning None if an overflow occurred
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// assert_eq!(
    ///     Duration::positive(1, 0).checked_add(Duration::positive(1, 0)),
    ///     Some(Duration::positive(2, 0))
    /// );
    /// assert_eq!(
    ///     Duration::positive(u64::MAX, 0).checked_add(Duration::positive(1, 0)),
    ///     None
    /// );
    /// assert_eq!(
    ///     Duration::negative(u64::MAX, 0).checked_add(Duration::negative(1, 0)),
    ///     None
    /// );
    /// ```
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

    /// Subtracts this duration with the `other` duration, returning None if an overflow occurred
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// assert_eq!(
    ///     Duration::positive(1, 0).checked_sub(Duration::positive(1, 0)),
    ///     Some(Duration::ZERO)
    /// );
    /// assert_eq!(
    ///     Duration::negative(u64::MAX, 0).checked_sub(Duration::positive(1, 0)),
    ///     None
    /// );
    /// ```
    #[inline]
    pub fn checked_sub(&self, other: Self) -> Option<Self> {
        self.checked_add(other.neg())
    }

    /// Saturating [`Duration`] addition. Computes `self + other`, returning [`Duration::MAX`] or
    /// [`Duration::MIN`] if an overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// assert_eq!(
    ///     Duration::positive(1, 0).saturating_add(Duration::positive(0, 1)),
    ///     Duration::positive(1, 1)
    /// );
    /// assert_eq!(
    ///     Duration::positive(u64::MAX, 0).saturating_add(Duration::positive(1, 0)),
    ///     Duration::MAX
    /// );
    /// ```
    pub fn saturating_add(&self, other: Self) -> Self {
        match self.checked_add(other) {
            Some(d) => d,
            // checked_add only returns None if both durations are either negative or positive so it
            // is enough to check one of the durations for negativity
            None if self.is_negative => Self::MIN,
            None => Self::MAX,
        }
    }

    /// Saturating [`Duration`] subtraction. Computes `self - other`, returning [`Duration::MAX`] or
    /// [`Duration::MIN`] if an overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu::Duration;
    ///
    /// assert_eq!(
    ///     Duration::positive(1, 0).saturating_sub(Duration::positive(1, 0)),
    ///     Duration::ZERO
    /// );
    /// assert_eq!(
    ///     Duration::negative(u64::MAX, 0).saturating_sub(Duration::positive(1, 0)),
    ///     Duration::MIN
    /// );
    /// ```
    #[inline]
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

/// Convert a [`std::time::Duration`] into a [`Duration`]
impl From<std::time::Duration> for Duration {
    fn from(duration: std::time::Duration) -> Self {
        Self {
            is_negative: false,
            inner: duration,
        }
    }
}

impl SaturatingInto<std::time::Duration> for Duration {
    fn saturating_into(self) -> std::time::Duration {
        self.try_into().unwrap_or_else(|error| match error {
            TryFromDurationError::NegativeDuration => std::time::Duration::ZERO,
            _ => unreachable!(), // cov:excl-line
        })
    }
}

/// Convert a [`Duration`] into a [`std::time::Duration`]
impl TryFrom<Duration> for std::time::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        if !duration.is_zero() && duration.is_negative {
            Err(TryFromDurationError::NegativeDuration)
        } else {
            Ok(duration.inner)
        }
    }
}

#[cfg(feature = "time")]
/// Convert a [`time::Duration`] into a [`Duration`]
///
/// [`time::Duration`]: <https://docs.rs/time/latest/time/struct.Duration.html>
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
/// Convert a [`Duration`] into a [`time::Duration`]
///
/// [`time::Duration`]: <https://docs.rs/time/latest/time/struct.Duration.html>
impl TryFrom<Duration> for time::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        (&duration).try_into()
    }
}

#[cfg(feature = "time")]
/// Convert a [`Duration`] into a [`time::Duration`]
///
/// [`time::Duration`]: <https://docs.rs/time/latest/time/struct.Duration.html>
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
        self.try_into().unwrap_or_else(|error| match error {
            TryFromDurationError::PositiveOverflow => time::Duration::MAX,
            TryFromDurationError::NegativeOverflow => time::Duration::MIN,
            _ => unreachable!(), // cov:excl-line
        })
    }
}

#[cfg(feature = "chrono")]
/// Convert a [`Duration`] into a [`chrono::Duration`]
impl TryFrom<Duration> for chrono::Duration {
    type Error = TryFromDurationError;

    fn try_from(duration: Duration) -> Result<Self, Self::Error> {
        (&duration).try_into()
    }
}

#[cfg(feature = "chrono")]
/// Convert a [`Duration`] into a [`chrono::Duration`]
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
        self.try_into().unwrap_or_else(|error| match error {
            TryFromDurationError::PositiveOverflow => chrono::Duration::max_value(),
            TryFromDurationError::NegativeOverflow => chrono::Duration::min_value(),
            _ => unreachable!(), // cov:excl-line
        })
    }
}

#[cfg(feature = "chrono")]
/// Convert a [`chrono::Duration`] into a [`Duration`]
impl From<chrono::Duration> for Duration {
    fn from(duration: chrono::Duration) -> Self {
        match duration.to_std() {
            Ok(inner) => Self {
                is_negative: false,
                inner,
            },
            Err(_) => Self {
                is_negative: true,
                inner: duration.abs().to_std().unwrap(),
            },
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
    use rstest_reuse::{apply, template};
    #[cfg(feature = "serde")]
    use serde_test::{assert_tokens, Token};

    use super::*;

    #[cfg(feature = "chrono")]
    const CHRONO_MIN_DURATION: Duration =
        Duration::negative(i64::MIN.unsigned_abs() / 1000, 808_000_000);
    #[cfg(feature = "chrono")]
    const CHRONO_MAX_DURATION: Duration = Duration::positive(i64::MAX as u64 / 1000, 807_000_000);

    #[cfg(feature = "serde")]
    #[test]
    fn test_time_unit_serde() {
        let time_unit = TimeUnit::Day;

        assert_tokens(
            &time_unit,
            &[
                Token::Enum { name: "TimeUnit" },
                Token::Str("Day"),
                Token::Unit,
            ],
        )
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_serde_multiplier() {
        let multiplier = Multiplier(1, 2);

        assert_tokens(
            &multiplier,
            &[
                Token::TupleStruct {
                    name: "Multiplier",
                    len: 2,
                },
                Token::I64(1),
                Token::I16(2),
                Token::TupleStructEnd,
            ],
        )
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_serde_duration() {
        let duration = Duration::positive(1, 2);

        assert_tokens(
            &duration,
            &[
                Token::Struct {
                    name: "Duration",
                    len: 2,
                },
                Token::Str("is_negative"),
                Token::Bool(false),
                Token::Str("inner"),
                Token::Struct {
                    name: "Duration",
                    len: 2,
                },
                Token::Str("secs"),
                Token::U64(1),
                Token::Str("nanos"),
                Token::U32(2),
                Token::StructEnd,
                Token::StructEnd,
            ],
        )
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
    fn test_multiplier_is_negative_and_is_positive(
        #[case] multi: Multiplier,
        #[case] expected: bool,
    ) {
        assert_eq!(multi.is_negative(), expected);
        assert_eq!(multi.is_positive(), !expected);
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
    #[case::positive_zero(Duration::positive(0, 0), true)]
    #[case::negative_zero(Duration::negative(0, 0), false)] // FIXME: This should return true
    #[case::positive_one(Duration::positive(1, 0), true)]
    #[case::negative_one(Duration::negative(1, 0), false)]
    fn test_fundu_duration_is_positive_and_is_negative(
        #[case] duration: Duration,
        #[case] expected: bool,
    ) {
        assert_eq!(duration.is_positive(), expected);
        assert_eq!(duration.is_negative(), !expected);
    }

    #[rstest]
    #[case::positive_zero(Duration::positive(0, 0), Duration::positive(0, 0))]
    #[case::negative_zero(Duration::negative(0, 0), Duration::positive(0, 0))]
    #[case::positive_one(Duration::positive(1, 0), Duration::positive(1, 0))]
    #[case::positive_one_nano(Duration::positive(0, 1), Duration::positive(0, 1))]
    #[case::negative_one(Duration::negative(1, 0), Duration::positive(1, 0))]
    #[case::negative_one_nano(Duration::negative(0, 1), Duration::positive(0, 1))]
    #[case::negative_one_one(Duration::negative(1, 1), Duration::positive(1, 1))]
    fn test_fundu_duration_abs(#[case] duration: Duration, #[case] expected: Duration) {
        assert_eq!(duration.abs(), expected);
    }

    #[template]
    #[rstest]
    #[case::both_standard_zero(Duration::ZERO, Duration::ZERO, Duration::ZERO)]
    #[case::both_positive_zero(
        Duration::positive(0, 0),
        Duration::positive(0, 0),
        Duration::positive(0, 0)
    )]
    #[case::both_negative_zero(Duration::negative(0, 0), Duration::negative(0, 0), Duration::ZERO)]
    #[case::one_add_zero(Duration::positive(1, 0), Duration::ZERO, Duration::positive(1, 0))]
    #[case::minus_one_add_zero(Duration::negative(1, 0), Duration::ZERO, Duration::negative(1, 0))]
    #[case::minus_one_add_plus_one(
        Duration::negative(1, 0),
        Duration::positive(1, 0),
        Duration::ZERO
    )]
    #[case::minus_one_add_plus_two_then_carry(
        Duration::negative(1, 0),
        Duration::positive(2, 0),
        Duration::positive(1, 0)
    )]
    #[case::minus_one_nano_add_one_then_carry(
        Duration::negative(0, 1),
        Duration::positive(1, 0),
        Duration::positive(0, 999_999_999)
    )]
    #[case::plus_one_nano_add_minus_one_then_carry(
        Duration::positive(0, 1),
        Duration::negative(1, 0),
        Duration::negative(0, 999_999_999)
    )]
    #[case::plus_one_add_minus_two_then_carry(
        Duration::positive(1, 0),
        Duration::negative(2, 0),
        Duration::negative(1, 0)
    )]
    #[case::one_sec_below_min_add_max(
        Duration::negative(u64::MAX - 1, 999_999_999),
        Duration::MAX,
        Duration::positive(1, 0),
    )]
    #[case::one_nano_below_min_add_max(
        Duration::negative(u64::MAX, 999_999_998),
        Duration::MAX,
        Duration::positive(0, 1)
    )]
    #[case::one_sec_below_max_add_min(
        Duration::positive(u64::MAX - 1, 999_999_999),
        Duration::MIN,
        Duration::negative(1, 0)
    )]
    #[case::one_nano_below_max_add_min(
        Duration::positive(u64::MAX, 999_999_998),
        Duration::MIN,
        Duration::negative(0, 1)
    )]
    #[case::min_and_max(Duration::MIN, Duration::MAX, Duration::ZERO)]
    fn test_fundu_duration_add_no_overflow_template(
        #[case] lhs: Duration,
        #[case] rhs: Duration,
        #[case] expected: Duration,
    ) {
    }

    #[apply(test_fundu_duration_add_no_overflow_template)]
    fn test_fundu_duration_add(lhs: Duration, rhs: Duration, expected: Duration) {
        assert_eq!(lhs + rhs, expected);
        assert_eq!(rhs + lhs, expected);
    }

    #[apply(test_fundu_duration_add_no_overflow_template)]
    fn test_fundu_duration_add_assign(lhs: Duration, rhs: Duration, expected: Duration) {
        let mut res = lhs;
        res += rhs;
        assert_eq!(res, expected);
        let mut res = rhs;
        res += lhs;
        assert_eq!(res, expected);
    }

    #[apply(test_fundu_duration_add_no_overflow_template)]
    fn test_fundu_duration_checked_add(lhs: Duration, rhs: Duration, expected: Duration) {
        assert_eq!(lhs.checked_add(rhs), Some(expected));
        assert_eq!(rhs.checked_add(lhs), Some(expected));
    }

    #[apply(test_fundu_duration_add_no_overflow_template)]
    fn test_fundu_duration_sub(lhs: Duration, rhs: Duration, expected: Duration) {
        assert_eq!(lhs - rhs.neg(), expected);
        assert_eq!(rhs - lhs.neg(), expected);
    }

    #[apply(test_fundu_duration_add_no_overflow_template)]
    fn test_fundu_duration_sub_assign(lhs: Duration, rhs: Duration, expected: Duration) {
        let mut res = lhs;
        res -= rhs.neg();
        assert_eq!(res, expected);
        let mut res = rhs;
        res -= lhs.neg();
        assert_eq!(res, expected);
    }

    #[apply(test_fundu_duration_add_no_overflow_template)]
    fn test_fundu_duration_checked_sub(lhs: Duration, rhs: Duration, expected: Duration) {
        assert_eq!(lhs.checked_sub(rhs.neg()), Some(expected));
        assert_eq!(rhs.checked_sub(lhs.neg()), Some(expected));
    }

    #[template]
    #[rstest]
    #[case::min(Duration::MIN, Duration::MIN)]
    #[case::min_minus_one(Duration::MIN, Duration::negative(1, 0))]
    #[case::min_minus_one_nano(Duration::MIN, Duration::negative(0, 1))]
    #[case::max(Duration::MAX, Duration::MAX)]
    #[case::max_plus_one(Duration::MAX, Duration::positive(1, 0))]
    #[case::max_plus_one_nano(Duration::MAX, Duration::positive(0, 1))]
    #[case::positive_middle_nano_overflow(
        Duration::positive(u64::MAX / 2 + 1, 999_999_999 / 2 + 1),
        Duration::positive(u64::MAX / 2, 999_999_999 / 2 + 1)
    )]
    #[case::positive_middle_secs_overflow(
        Duration::positive(u64::MAX / 2 + 1, 999_999_999 / 2 + 1),
        Duration::positive(u64::MAX / 2 + 1, 999_999_999 / 2)
    )]
    #[case::negative_middle_nano_overflow(
        Duration::negative(u64::MAX / 2 + 1, 999_999_999 / 2 + 1),
        Duration::negative(u64::MAX / 2, 999_999_999 / 2 + 1)
    )]
    #[case::negative_middle_secs_overflow(
        Duration::negative(u64::MAX / 2 + 1, 999_999_999 / 2 + 1),
         Duration::negative(u64::MAX / 2 + 1, 999_999_999 / 2)
    )]
    fn test_fundu_duration_add_overflow_template(#[case] lhs: Duration, #[case] rhs: Duration) {}

    #[apply(test_fundu_duration_add_overflow_template)]
    #[should_panic = "Overflow when adding duration"]
    fn test_fundu_duration_add_and_add_assign_then_overflow(mut lhs: Duration, rhs: Duration) {
        lhs += rhs;
    }

    #[apply(test_fundu_duration_add_overflow_template)]
    #[should_panic = "Overflow when subtracting duration"]
    #[allow(clippy::no_effect)]
    fn test_fundu_duration_sub_and_sub_assign_then_overflow(mut lhs: Duration, rhs: Duration) {
        lhs -= rhs.neg();
    }

    #[apply(test_fundu_duration_add_overflow_template)]
    fn test_fundu_duration_checked_add_then_overflow(lhs: Duration, rhs: Duration) {
        assert_eq!(lhs.checked_add(rhs), None);
        assert_eq!(rhs.checked_add(lhs), None);
    }

    #[apply(test_fundu_duration_add_overflow_template)]
    fn test_fundu_duration_checked_sub_then_overflow(lhs: Duration, rhs: Duration) {
        assert_eq!(lhs.checked_sub(rhs.neg()), None);
    }

    #[apply(test_fundu_duration_add_overflow_template)]
    fn test_fundu_duration_saturating_add_then_saturate(lhs: Duration, rhs: Duration) {
        let expected = if lhs.checked_add(rhs).is_none() && lhs.is_positive() && rhs.is_positive() {
            Duration::MAX
        } else {
            Duration::MIN
        };
        assert_eq!(lhs.saturating_add(rhs), expected);
        assert_eq!(rhs.saturating_add(lhs), expected);
    }

    #[apply(test_fundu_duration_add_overflow_template)]
    fn test_fundu_duration_saturating_sub_then_saturate(lhs: Duration, rhs: Duration) {
        let expected =
            if lhs.checked_sub(rhs.neg()).is_none() && lhs.is_negative() && rhs.neg().is_positive()
            {
                Duration::MIN
            } else {
                Duration::MAX
            };
        assert_eq!(lhs.saturating_sub(rhs.neg()), expected);
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

    #[rstest]
    #[case::positive_zero(Duration::ZERO, StdDuration::ZERO)]
    #[case::negative_zero(Duration::negative(0, 0), StdDuration::ZERO)]
    #[case::positive_one(Duration::positive(1, 0), StdDuration::new(1, 0))]
    #[case::positive_one_nano(Duration::positive(0, 1), StdDuration::new(0, 1))]
    #[case::negative_one(Duration::negative(1, 0), StdDuration::ZERO)]
    #[case::negative_one_nano(Duration::negative(0, 1), StdDuration::ZERO)]
    #[case::max(Duration::MAX, StdDuration::MAX)]
    fn test_fundu_duration_saturating_into_std_duration(
        #[case] duration: Duration,
        #[case] expected: StdDuration,
    ) {
        assert_eq!(
            SaturatingInto::<std::time::Duration>::saturating_into(duration),
            expected
        );
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

    #[cfg(feature = "chrono")]
    #[rstest]
    #[case::positive_zero(Duration::ZERO, chrono::Duration::zero())]
    #[case::negative_zero(Duration::negative(0, 0), chrono::Duration::zero())]
    #[case::positive_one(Duration::positive(1, 0), chrono::Duration::seconds(1))]
    #[case::negative_one(Duration::negative(1, 0), chrono::Duration::seconds(-1))]
    #[case::negative_barely_no_overflow(
        Duration::negative(i64::MIN.unsigned_abs() / 1000, 808_000_000),
        chrono::Duration::min_value()
    )]
    #[case::negative_barely_overflow(
        Duration::negative(i64::MIN.unsigned_abs() / 1000 + 1, 0),
        chrono::Duration::min_value()
    )]
    #[case::negative_max_overflow(
        Duration::negative(u64::MAX, 999_999_999),
        chrono::Duration::min_value()
    )]
    #[case::positive_barely_no_overflow(
        Duration::positive(i64::MAX as u64 / 1000, 807_000_000),
        chrono::Duration::max_value()
    )]
    #[case::positive_barely_overflow(
        Duration::positive(i64::MAX as u64 / 1000 + 1, 807_000_000),
        chrono::Duration::max_value()
    )]
    #[case::positive_max_overflow(
        Duration::positive(u64::MAX, 999_999_999),
        chrono::Duration::max_value()
    )]
    fn test_fundu_duration_saturating_into_chrono_duration(
        #[case] duration: Duration,
        #[case] expected: chrono::Duration,
    ) {
        assert_eq!(
            SaturatingInto::<chrono::Duration>::saturating_into(duration),
            expected
        );
    }

    #[rstest]
    #[case::negative_one(Duration::negative(1, 0))]
    #[case::negative_one_nano(Duration::negative(0, 1))]
    #[case::one_one(Duration::negative(1, 1))]
    #[case::min(Duration::MIN)]
    fn test_std_duration_try_from_for_fundu_duration_then_error(#[case] duration: Duration) {
        assert_eq!(
            TryInto::<std::time::Duration>::try_into(duration).unwrap_err(),
            TryFromDurationError::NegativeDuration
        );
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
    fn test_chrono_duration_try_from_fundu_duration(
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
    fn test_chrono_duration_try_from_fundu_duration_then_error(
        #[case] duration: Duration,
        #[case] expected: TryFromDurationError,
    ) {
        let result: Result<ChronoDuration, TryFromDurationError> = duration.try_into();
        assert_eq!(result.unwrap_err(), expected)
    }

    #[cfg(feature = "time")]
    #[test]
    fn test_time_duration_try_from_fundu_duration() {
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
    fn test_fundu_duration_from_std_time_duration(
        #[case] std_duration: std::time::Duration,
        #[case] expected: Duration,
    ) {
        assert_eq!(Duration::from(std_duration), expected);
    }

    #[cfg(feature = "time")]
    #[rstest]
    #[case::zero(time::Duration::ZERO, Duration::ZERO)]
    #[case::positive_one(time::Duration::new(1, 0), Duration::positive(1, 0))]
    #[case::positive_one_nano(time::Duration::new(0, 1), Duration::positive(0, 1))]
    #[case::negative_one(time::Duration::new(-1, 0), Duration::negative(1, 0))]
    #[case::negative_one_nano(time::Duration::new(0, -1), Duration::negative(0, 1))]
    #[case::positive_one_negative_one_nano(
        time::Duration::new(1, -1),
        Duration::positive(0, 999_999_999)
    )]
    #[case::negative_one_positive_one_nano(
        time::Duration::new(-1, 1),
        Duration::negative(0, 999_999_999)
    )]
    #[case::min(time::Duration::MIN, Duration::negative(i64::MIN.unsigned_abs(), 999_999_999))]
    #[case::max(time::Duration::MAX, Duration::positive(i64::MAX as u64, 999_999_999))]
    fn test_fundu_duration_from_time_duration(
        #[case] time_duration: time::Duration,
        #[case] expected: Duration,
    ) {
        assert_eq!(Duration::from(time_duration), expected);
    }

    #[cfg(feature = "chrono")]
    #[rstest]
    #[case::zero(chrono::Duration::zero(), Duration::ZERO)]
    #[case::positive_one(chrono::Duration::seconds(1), Duration::positive(1, 0))]
    #[case::positive_one_nano(chrono::Duration::nanoseconds(1), Duration::positive(0, 1))]
    #[case::negative_one(chrono::Duration::seconds(-1), Duration::negative(1, 0))]
    #[case::negative_one_nano(chrono::Duration::nanoseconds(-1), Duration::negative(0, 1))]
    #[case::min(chrono::Duration::min_value(), CHRONO_MIN_DURATION)]
    #[case::max(chrono::Duration::max_value(), CHRONO_MAX_DURATION)]
    fn test_fundu_duration_from_chrono_duration(
        #[case] chrono_duration: chrono::Duration,
        #[case] expected: Duration,
    ) {
        assert_eq!(Duration::from(chrono_duration), expected)
    }
}
