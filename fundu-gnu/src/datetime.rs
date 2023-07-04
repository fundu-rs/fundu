// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::ops::Neg;
use std::time::{Duration as StdDuration, SystemTime};

#[cfg(feature = "chrono")]
use chrono::{Datelike, Timelike};
use fundu_core::time::Duration;
#[cfg(feature = "time")]
use time::{OffsetDateTime, PrimitiveDateTime};

use crate::util::{self, floor_div};

const DAYS_IN_PREVIOUS_MONTH: [u16; 12] = [306, 337, 0, 31, 61, 92, 122, 153, 184, 214, 245, 275];
const ORDINAL_TO_MONTH: [u8; 366] = [
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5,
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6,
    6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 8,
    8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
    11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
    11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
];

const NANOS_PER_SEC_I64: i64 = 1_000_000_000;
const NANOS_PER_SEC_U64: u64 = NANOS_PER_SEC_I64 as u64;
const NANOS_PER_SEC_U128: u128 = NANOS_PER_SEC_I64 as u128;
const NANOS_PER_DAY_I64: i64 = 86_400_000_000_000;
const NANOS_PER_DAY_I128: i128 = NANOS_PER_DAY_I64 as i128;

const SECS_PER_MINUTE_I64: i64 = 60;
const SECS_PER_MINUTE_U64: u64 = SECS_PER_MINUTE_I64 as u64;
const SECS_PER_HOUR_I64: i64 = 3600;
const SECS_PER_HOUR_U64: u64 = SECS_PER_HOUR_I64 as u64;

const JD_BASE: i64 = 1_721_119;

/// Store a proleptic gregorian date as [`JulianDay`]
///
/// The Julian Day Number or Julian Day is the number of days since noon UTC on November 24 of the
/// year -4713 in the Gregorian Calendar. The year 0 equals 1BC. The JD number is a possibly
/// negative integer representing the number of whole days since the reference instant to noon of
/// that day. This `JulianDay` implementation does not have a fraction and stores the day as if no
/// time was specified which is equivalent of a time being always __noon__.
///
/// # Examples
///
/// ```rust
/// use fundu_gnu::JulianDay;
///
/// assert_eq!(JulianDay(0).to_gregorian(), Some((-4713, 11, 24)));
/// assert_eq!(JulianDay(-365).to_gregorian(), Some((-4714, 11, 24)));
/// assert_eq!(JulianDay(1_721_060).to_gregorian(), Some((0, 1, 1)));
/// assert_eq!(JulianDay(2_440_588).to_gregorian(), Some((1970, 1, 1)));
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JulianDay(pub i64);

impl JulianDay {
    /// Calculate the `JulianDay` from a proleptic gregorian date
    ///
    /// For a non-panicking version see [`JulianDay::try_from_gregorian`].
    ///
    /// # Panics
    ///
    /// Panics if the input arguments are invalid. Valid ranges are:
    ///
    /// * `1 <= month <= 12`
    /// * `1 <= day <= 31`
    ///
    /// or an overflow occurred. Use the safer alternative [`JulianDay::try_from_gregorian`] if very
    /// high values for years are expected.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::JulianDay;
    ///
    /// assert_eq!(JulianDay::from_gregorian(-4713, 11, 24), JulianDay(0));
    /// assert_eq!(JulianDay::from_gregorian(-4714, 11, 24), JulianDay(-365));
    /// assert_eq!(JulianDay::from_gregorian(0, 1, 1), JulianDay(1_721_060));
    /// assert_eq!(JulianDay::from_gregorian(1970, 1, 1), JulianDay(2440588));
    /// ```
    pub const fn from_gregorian(year: i64, month: u8, day: u8) -> Self {
        match Self::try_from_gregorian(year, month, day) {
            Some(jd) => jd,
            None => panic!("Overflow calculating julian day from gregorian date"),
        }
    }

    /// Calculate the `JulianDay` from a proleptic gregorian date
    ///
    /// Returns None if an overflow occurred most likely to a year greater than approximately
    /// `25_200_470_046_046_596` or smaller than approximately `-25_200_470_046_046_596`
    ///
    /// This method is based on the work of Peter Baum and his publication of
    /// [Date Algorithms](https://www.researchgate.net/publication/316558298_Date_Algorithms).
    ///
    /// # Panics
    ///
    /// Panics if the input arguments are invalid. Valid ranges are:
    ///
    /// * `1 <= month <= 12`
    /// * `1 <= day <= 31`
    ///
    /// Note it is not an error to specify `day = 31` for example for the month 4 (April). In such a
    /// case the month is assumed to be the next month (here May) and `day = 1`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::JulianDay;
    ///
    /// assert_eq!(
    ///     JulianDay::try_from_gregorian(-4713, 11, 24),
    ///     Some(JulianDay(0))
    /// );
    /// assert_eq!(
    ///     JulianDay::try_from_gregorian(-4714, 11, 24),
    ///     Some(JulianDay(-365))
    /// );
    /// assert_eq!(
    ///     JulianDay::try_from_gregorian(0, 1, 1),
    ///     Some(JulianDay(1_721_060))
    /// );
    /// assert_eq!(
    ///     JulianDay::try_from_gregorian(1970, 1, 1),
    ///     Some(JulianDay(2440588))
    /// );
    /// ```
    pub const fn try_from_gregorian(year: i64, month: u8, day: u8) -> Option<Self> {
        validate!(month, 1, 12);
        validate!(day, 1, 31);

        let year = if month < 3 {
            match year.checked_sub(1) {
                Some(y) => y,
                None => return None,
            }
        } else {
            year
        };

        if let Some(y) = year.checked_mul(365) {
            if let Some(y) = y.checked_add(
                day as i64
                    + DAYS_IN_PREVIOUS_MONTH[(month - 1) as usize] as i64
                    + floor_div(year, 4)
                    - floor_div(year, 100)
                    + floor_div(year, 400)
                    + JD_BASE,
            ) {
                return Some(Self(y));
            }
        }
        None
    }

    /// Return the julian day
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::JulianDay;
    ///
    /// assert_eq!(JulianDay(-1).as_days(), -1);
    /// ```
    pub const fn as_days(self) -> i64 {
        self.0
    }

    /// Calculate the proleptic gregorian date from this `JulianDay`
    ///
    /// The method returns None if an overflow occurred.
    ///
    /// This method is based on the work of Peter Baum and his publication of
    /// [Date Algorithms](https://www.researchgate.net/publication/316558298_Date_Algorithms).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::JulianDay;
    ///
    /// assert_eq!(JulianDay(-365).to_gregorian(), Some((-4714, 11, 24)));
    /// assert_eq!(JulianDay(0).to_gregorian(), Some((-4713, 11, 24)));
    /// assert_eq!(JulianDay(1721060).to_gregorian(), Some((0, 1, 1)));
    /// assert_eq!(JulianDay(2440588).to_gregorian(), Some((1970, 1, 1)));
    /// ```
    #[allow(clippy::missing_panics_doc)]
    pub fn to_gregorian(self) -> Option<(i64, u8, u8)> {
        let zero = self.0.checked_sub(JD_BASE)?;
        let c = zero.checked_mul(100)? - 25;
        // Calculate the number of full centuries in the Gregorian Calendar
        let full_centuries = floor_div(c, 3_652_425);
        // Calculate the days within the whole centuries in the Julian Calendar by adding back days
        // removed in the Gregorian Calendar
        let days_centuries = full_centuries - floor_div(full_centuries, 4);

        // Calculate the year in a calendar whose years start on March 1
        let year = floor_div((100 * days_centuries).checked_add(c)?, 36525);

        // Calculate the value of the day count in the current year
        // unwrap is safe since 1 <= ordinal <= 366
        let ordinal =
            u16::try_from(days_centuries + zero - 365 * year - floor_div(year, 4)).unwrap();

        // Calculate the value of the month in the current year using a lookup table
        // unwrap is safe since 1 <= month <= 12
        let month = ORDINAL_TO_MONTH[usize::from(ordinal - 1)];

        // Calculate the day of the month using a lookup table
        // unwrap is safe since 1 <= day <= 31
        let day = u8::try_from(ordinal - DAYS_IN_PREVIOUS_MONTH[usize::from(month - 1)]).unwrap();

        // Convert the month and year to a calendar starting January 1 and return the result
        if month < 3 {
            Some((year + 1, month, day))
        } else {
            Some((year, month, day))
        }
    }

    /// Checked days addition. Computes `self.0 + days`, returning None if an overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::JulianDay;
    ///
    /// assert_eq!(
    ///     JulianDay(0).checked_add_days(10_000),
    ///     Some(JulianDay(10_000))
    /// );
    /// assert_eq!(JulianDay(0).checked_add_days(-1), Some(JulianDay(-1)));
    /// ```
    pub const fn checked_add_days(self, days: i64) -> Option<Self> {
        match self.0.checked_add(days) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }

    /// Checked days subtraction. Computes `self.0 - days`, returning None if an overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::JulianDay;
    ///
    /// assert_eq!(
    ///     JulianDay(1_700_000).checked_sub_days(1),
    ///     Some(JulianDay(1_699_999))
    /// );
    /// assert_eq!(JulianDay(0).checked_sub_days(366), Some(JulianDay(-366)));
    /// ```
    pub const fn checked_sub_days(self, days: i64) -> Option<Self> {
        match self.0.checked_sub(days) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }

    /// Checked addition. Computes `self + rhs`, returning None if an overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::JulianDay;
    ///
    /// assert_eq!(
    ///     JulianDay(0).checked_add(JulianDay(10_000)),
    ///     Some(JulianDay(10_000))
    /// );
    /// assert_eq!(JulianDay(0).checked_add(JulianDay(-1)), Some(JulianDay(-1)));
    /// ```
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        match self.0.checked_add(rhs.0) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }

    /// Checked subtraction. Computes `self - rhs`, returning None if an overflow occurred.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::JulianDay;
    ///
    /// assert_eq!(
    ///     JulianDay(1_700_000).checked_sub(JulianDay(1)),
    ///     Some(JulianDay(1_699_999))
    /// );
    /// assert_eq!(
    ///     JulianDay(0).checked_sub(JulianDay(366)),
    ///     Some(JulianDay(-366))
    /// );
    /// ```
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        match self.0.checked_sub(rhs.0) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }
}

/// Proleptic gregorian date and time with fast calculations of differences in date and time
///
/// This struct is primarily designed to provide fast calculations of possibly very large
/// differences in date and time in the proleptic gregorian calendar. It is a superset of date and
/// time structs like [`time::PrimitiveDateTime`], [`time::OffsetDateTime`] which is limited to
/// years ranging from `-999_999` to `999_999` if the `large-dates` feature is activated and
/// [`chrono::DateTime`] which is limited to years ranging from `-262_144` to `262_143`. Since gnu
/// supports much larger dates, and to provide maximum possible compatibility with `gnu`, this
/// struct provides support for dates ranging from approximately `-583_344_214_028` years to
/// `583_344_214_028` years which is far more than the age of the universe.
///
/// This struct implements `From<OffsetDateTime>` and `From<PrimitiveDateTime>` if the `time`
/// feature is activated. If the `chrono` feature is activated `From<DateTime>` is available.
///
/// # Examples
///
/// ```rust
/// use fundu_gnu::DateTime;
///
/// let date_time = DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0);
/// assert_eq!(date_time, DateTime::UNIX_EPOCH);
/// ```
///
/// If the `chrono` feature is activated a chrono date and time can be converted lossless to a
/// `DateTime`
#[cfg_attr(feature = "chrono", doc = "```rust")]
#[cfg_attr(not(feature = "chrono"), doc = "```rust,ignore")]
/// use chrono::{FixedOffset, TimeZone};
/// use fundu_gnu::DateTime;
///
/// let chrono_date = FixedOffset::east_opt(0)
///     .unwrap()
///     .with_ymd_and_hms(2000, 12, 31, 23, 59, 59)
///     .unwrap();
/// assert_eq!(
///     DateTime::from(chrono_date),
///     DateTime::from_gregorian_date_time(2000, 12, 31, 23, 59, 59, 0)
/// );
///
/// // Now with an offset
/// let chrono_date = FixedOffset::east_opt(2 * 3600)
///     .unwrap()
///     .with_ymd_and_hms(2000, 12, 31, 23, 59, 59)
///     .unwrap();
/// assert_eq!(
///     DateTime::from(chrono_date),
///     DateTime::from_gregorian_date_time(2000, 12, 31, 21, 59, 59, 0)
/// );
/// ```
///
/// And if the `time` feature is activated:
#[cfg_attr(feature = "time", doc = "```rust")]
#[cfg_attr(not(feature = "time"), doc = "```rust,ignore")]
/// use time::macros::{datetime, offset};
/// use fundu_gnu::DateTime;
///
/// assert_eq!(
///     DateTime::from(datetime!(2000-12-31 23:59:59.200_000_000)),
///     DateTime::from_gregorian_date_time(2000, 12, 31, 23, 59, 59, 200_000_000)
/// );
///
/// // And with an offset
/// assert_eq!(
///     DateTime::from(datetime!(2000-12-31 23:59:59.200_000_000 UTC).to_offset(offset!(-2))),
///     DateTime::from_gregorian_date_time(2000, 12, 31, 21, 59, 59, 200_000_000)
/// );
/// ```
///
/// [`time::PrimitiveDateTime`]: https://docs.rs/time/latest/time/struct.PrimitiveDateTime.html
/// [`time::OffsetDateTime`]: https://docs.rs/time/latest/time/struct.OffsetDateTime.html
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DateTime {
    days: JulianDay,
    time: u64,
}

impl DateTime {
    /// The `DateTime` of the unix epoch in UTC +0
    pub const UNIX_EPOCH: Self = Self::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0);

    /// Create a `DateTime` from a given proleptic gregorian date and time
    ///
    /// # Panics
    ///
    /// This method panics if the input arguments are invalid. Valid ranges are:
    ///
    /// * `1 <= month <= 12`
    /// * `1 <= day <= 31`
    /// * `0 <= hour <= 23`
    /// * `0 <= minute <= 59`
    /// * `0 <= second <= 59`
    /// * `0 <= nanos <= 999_999_999`
    ///
    /// Note it is not an error to specify `day = 31` for example for the month 4 (April). In such a
    /// case the month is assumed to be the next month (here May) and `day = 1`.
    ///
    /// In theory, the year may not exceed approximately `25_200_470_046_046_596` or
    /// `-25_200_470_046_046_596` years within this function or else a panic occurs. To be sure that
    /// the year doesn't cause overflows and returning `None` from other functions of `DateTime`, a
    /// safer range is `-583_344_214_028` to `583_344_214_028` years.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::DateTime;
    ///
    /// assert_eq!(
    ///     DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
    ///     DateTime::UNIX_EPOCH
    /// );
    ///
    /// // 1972 is a leap year
    /// let date_time = DateTime::from_gregorian_date_time(1972, 2, 29, 1, 30, 59, 700_000_000);
    /// assert_eq!(
    ///     date_time.to_gregorian_date_time(),
    ///     Some((1972, 2, 29, 1, 30, 59, 700_000_000))
    /// );
    ///
    /// // Given 1960-4-31, the day carries over into the next month
    /// assert_eq!(
    ///     DateTime::from_gregorian_date_time(1960, 4, 31, 1, 30, 59, 700_000_000),
    ///     DateTime::from_gregorian_date_time(1960, 5, 1, 1, 30, 59, 700_000_000),
    /// );
    /// ```
    pub const fn from_gregorian_date_time(
        year: i64,
        month: u8,
        day: u8,
        hour: u8,
        minute: u8,
        second: u8,
        nanos: u32,
    ) -> Self {
        validate!(hour <= 23);
        validate!(minute <= 59);
        validate!(second <= 59);
        validate!(nanos <= 999_999_999);

        let days = JulianDay::from_gregorian(year, month, day);
        let time = {
            (hour as u64 * SECS_PER_HOUR_U64 + minute as u64 * SECS_PER_MINUTE_U64 + second as u64)
                * NANOS_PER_SEC_U64
                + nanos as u64
        };
        Self { days, time }
    }

    /// Return the proleptic gregorian date
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::DateTime;
    ///
    /// assert_eq!(DateTime::UNIX_EPOCH.to_gregorian_date(), Some((1970, 1, 1)));
    /// assert_eq!(
    ///     DateTime::from_gregorian_date_time(1959, 1, 12, 10, 3, 59, 0).to_gregorian_date(),
    ///     Some((1959, 1, 12))
    /// );
    /// ```
    pub fn to_gregorian_date(&self) -> Option<(i64, u8, u8)> {
        self.days.to_gregorian()
    }

    /// Return the proleptic gregorian date and time
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::DateTime;
    ///
    /// assert_eq!(
    ///     DateTime::UNIX_EPOCH.to_gregorian_date_time(),
    ///     Some((1970, 1, 1, 0, 0, 0, 0))
    /// );
    /// assert_eq!(
    ///     DateTime::from_gregorian_date_time(1959, 1, 12, 10, 3, 59, 500_000_000)
    ///         .to_gregorian_date_time(),
    ///     Some((1959, 1, 12, 10, 3, 59, 500_000_000))
    /// );
    /// ```
    pub fn to_gregorian_date_time(&self) -> Option<(i64, u8, u8, u8, u8, u8, u32)> {
        let (year, month, day) = self.days.to_gregorian()?;
        let (h, m, s, n) = self.as_hmsn();
        Some((year, month, day, h, m, s, n))
    }

    /// Return the time as tuple with (hour, minute, second, nanos)
    ///
    /// This method cannot fail
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::DateTime;
    ///
    /// assert_eq!(DateTime::UNIX_EPOCH.as_hmsn(), (0, 0, 0, 0));
    /// assert_eq!(
    ///     DateTime::from_gregorian_date_time(1959, 1, 12, 10, 3, 59, 500_000_000).as_hmsn(),
    ///     (10, 3, 59, 500_000_000)
    /// );
    /// ```
    pub const fn as_hmsn(&self) -> (u8, u8, u8, u32) {
        let mut time = self.time;

        #[allow(clippy::cast_sign_loss)]
        let nanos = (time % NANOS_PER_SEC_U64) as u32;
        time /= NANOS_PER_SEC_U64;
        let hour = time / SECS_PER_HOUR_U64;
        time %= SECS_PER_HOUR_U64;
        let min = time / SECS_PER_MINUTE_U64;
        time %= SECS_PER_MINUTE_U64;

        #[allow(clippy::cast_possible_truncation)]
        #[allow(clippy::cast_sign_loss)]
        (hour as u8, min as u8, time as u8, nanos)
    }

    /// Return the proleptic gregorian date as [`JulianDay`]
    ///
    /// This `JulianDay` implementation does not have a fraction and returns the day as if no time
    /// was specified which is equivalent of a time being always __noon__
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{DateTime, JulianDay};
    ///
    /// assert_eq!(DateTime::UNIX_EPOCH.as_julian_day(), JulianDay(2_440_588));
    /// assert_eq!(
    ///     DateTime::from_gregorian_date_time(-4713, 11, 24, 10, 3, 59, 500_000_000).as_julian_day(),
    ///     JulianDay(0)
    /// );
    /// assert_eq!(
    ///     DateTime::from_gregorian_date_time(2023, 3, 9, 23, 59, 59, 999_999_999).as_julian_day(),
    ///     JulianDay(2460013)
    /// );
    /// ```
    pub const fn as_julian_day(&self) -> JulianDay {
        self.days
    }

    fn now_utc_with_system_time(now: SystemTime) -> Self {
        let date_unix_epoch = Self::UNIX_EPOCH;
        match now.duration_since(SystemTime::UNIX_EPOCH) {
            Ok(duration) => date_unix_epoch
                .checked_add_duration(&duration.into())
                .expect("Overflow when adding current system time difference to unix epoch"),
            Err(error) => date_unix_epoch
                .checked_add_duration(&Duration::from_std(true, error.duration()))
                .expect("Overflow when subtracting current system time difference from unix epoch"),
        }
    }

    /// Return the current `DateTime` with an offset of UTC +-0
    ///
    /// # Platform-specific behavior
    ///
    /// This method is subject to the same
    /// [restrictions](https://doc.rust-lang.org/nightly/std/time/struct.SystemTime.html#platform-specific-behavior)
    /// as [`SystemTime`] does.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::DateTime;
    ///
    /// let now = DateTime::now_utc();
    /// ```
    pub fn now_utc() -> Self {
        Self::now_utc_with_system_time(util::now())
    }

    /// Add a [`Duration`] to the `DateTime` returning some new `DateTime` or `None` on overflow
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{DateTime, Duration};
    ///
    /// let date_time = DateTime::from_gregorian_date_time(1970, 1, 1, 23, 59, 59, 0);
    /// assert_eq!(
    ///     date_time.checked_add_duration(&Duration::positive(3600, 0)),
    ///     Some(DateTime::from_gregorian_date_time(1970, 1, 2, 0, 59, 59, 0))
    /// );
    /// ```
    #[allow(clippy::missing_panics_doc)]
    pub fn checked_add_duration(self, duration: &Duration) -> Option<Self> {
        let mut duration = *duration;
        let days = duration.extract_days();

        self.days.checked_add_days(days).and_then(|jd| {
            // The unwrap is safe here because we extracted the days
            let nanos = i64::try_from(duration.as_nanos()).unwrap();

            // The unwrap is safe here because 0 <= time <= 85_399_999_999_999
            let time = i64::try_from(self.time).unwrap() + nanos;
            // -85_399_999_999_999 <= time <= 2 * 85_399_999_999_999
            if time < 0 {
                jd.checked_add_days(-1).map(|jd| Self {
                    days: jd,
                    time: u64::try_from(time + NANOS_PER_DAY_I64).unwrap(),
                })
            } else if time < NANOS_PER_DAY_I64 {
                Some(Self {
                    days: jd,
                    time: u64::try_from(time).unwrap(),
                })
            } else {
                jd.checked_add_days(1).map(|jd| Self {
                    days: jd,
                    time: u64::try_from(time - NANOS_PER_DAY_I64).unwrap(),
                })
            }
        })
    }

    /// Subtract a [`Duration`] from the `DateTime`
    ///
    /// This method returns some new `DateTime` or `None` on overflow
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{DateTime, Duration};
    ///
    /// let date_time = DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0);
    /// assert_eq!(
    ///     date_time.checked_sub_duration(&Duration::positive(3600, 0)),
    ///     Some(DateTime::from_gregorian_date_time(
    ///         1969, 12, 31, 23, 0, 0, 0
    ///     ))
    /// );
    /// ```
    pub fn checked_sub_duration(self, duration: &Duration) -> Option<Self> {
        self.checked_add_duration(&duration.neg())
    }

    /// Add years, months and days to the `DateTime` in the proleptic gregorian calendar
    ///
    /// This method returns some new `DateTime` or `None` on overflow
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{DateTime, Duration};
    ///
    /// let date_time = DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0);
    /// assert_eq!(
    ///     date_time.checked_add_gregorian(2000, 0, 0),
    ///     Some(DateTime::from_gregorian_date_time(3970, 1, 1, 0, 0, 0, 0))
    /// );
    ///
    /// let date_time = DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0);
    /// assert_eq!(
    ///     date_time.checked_add_gregorian(0, 121, 0),
    ///     Some(DateTime::from_gregorian_date_time(1980, 2, 1, 0, 0, 0, 0))
    /// );
    ///
    /// let date_time = DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0);
    /// assert_eq!(
    ///     date_time.checked_add_gregorian(0, 0, 365),
    ///     Some(DateTime::from_gregorian_date_time(1971, 1, 1, 0, 0, 0, 0))
    /// );
    ///
    /// // 1972 is a leap year
    /// let date_time = DateTime::from_gregorian_date_time(1972, 1, 1, 0, 0, 0, 0);
    /// assert_eq!(
    ///     date_time.checked_add_gregorian(0, 0, 366),
    ///     Some(DateTime::from_gregorian_date_time(1973, 1, 1, 0, 0, 0, 0))
    /// );
    /// ```
    #[allow(clippy::missing_panics_doc)]
    pub fn checked_add_gregorian(self, years: i64, months: i64, days: i64) -> Option<Self> {
        let (year, month, day) = self.days.to_gregorian()?;
        let (month, years) = years.checked_add(months / 12).and_then(|y| {
            // now.month() is 1-based, we need it 0-based for now
            let month = i8::try_from(months % 12).unwrap() + i8::try_from(month).unwrap() - 1;
            if month < 0 {
                y.checked_sub(1)
                    .map(|y| (u8::try_from(month + 12).unwrap(), y))
            } else if month < 12 {
                Some((u8::try_from(month).unwrap(), y))
            } else {
                y.checked_add(1)
                    .map(|y| (u8::try_from(month - 12).unwrap(), y))
            }
        })?;

        year.checked_add(years).and_then(|year| {
            JulianDay::try_from_gregorian(year, month + 1, day).and_then(|jd| {
                jd.checked_add_days(days).map(|jd| Self {
                    days: jd,
                    time: self.time,
                })
            })
        })
    }

    /// Calculate the [`Duration`] between this `DateTime` and another `DateTime`
    ///
    /// If the other `DateTime` is greater than this `DateTime` the [`Duration`] is negative. This
    /// method returns `None` when an overflow occurs.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use fundu_gnu::{DateTime, Duration};
    ///
    /// let dt = DateTime::from_gregorian_date_time(1971, 1, 1, 23, 0, 0, 0);
    /// assert_eq!(
    ///     dt.duration_since(DateTime::UNIX_EPOCH),
    ///     Some(Duration::positive(365 * 86400 + 23 * 3600, 0))
    /// );
    ///
    /// let dt = DateTime::from_gregorian_date_time(1973, 1, 1, 0, 0, 10, 123_456_789);
    /// let other = DateTime::from_gregorian_date_time(1972, 1, 1, 0, 0, 0, 0);
    /// assert_eq!(
    ///     dt.duration_since(other),
    ///     Some(Duration::positive(366 * 86400 + 10, 123_456_789))
    /// );
    /// assert_eq!(
    ///     other.duration_since(dt),
    ///     Some(Duration::negative(366 * 86400 + 10, 123_456_789))
    /// );
    /// ```
    #[allow(clippy::missing_panics_doc)]
    pub fn duration_since(self, rhs: Self) -> Option<Duration> {
        let jd = self.days.checked_sub(rhs.days)?;
        let time = i64::try_from(self.time)
            .unwrap()
            .checked_sub(i64::try_from(rhs.time).unwrap())?;

        let total = i128::from(jd.as_days())
            .checked_mul(NANOS_PER_DAY_I128)
            .and_then(|t| t.checked_add(i128::from(time)))?;
        let is_negative = total.is_negative();
        let total = total.unsigned_abs();

        let secs = u64::try_from(total / NANOS_PER_SEC_U128).ok()?;
        let nanos = u32::try_from(total % NANOS_PER_SEC_U128).unwrap();
        Some(Duration::from_std(
            is_negative,
            StdDuration::new(secs, nanos),
        ))
    }
}

#[cfg(feature = "time")]
impl From<OffsetDateTime> for DateTime {
    fn from(value: OffsetDateTime) -> Self {
        let (year, month, day) = value.to_calendar_date();
        let (h, m, s, n) = value.to_hms_nano();
        Self::from_gregorian_date_time(
            i64::from(year),
            u8::try_from(month).unwrap(),
            day,
            h,
            m,
            s,
            n,
        )
    }
}

#[cfg(feature = "time")]
impl From<PrimitiveDateTime> for DateTime {
    fn from(value: PrimitiveDateTime) -> Self {
        value.assume_utc().into()
    }
}

#[cfg(feature = "chrono")]
impl<T: chrono::TimeZone> From<chrono::DateTime<T>> for DateTime {
    fn from(value: chrono::DateTime<T>) -> Self {
        value.naive_utc().into()
    }
}

#[cfg(feature = "chrono")]
impl From<chrono::NaiveDateTime> for DateTime {
    fn from(value: chrono::NaiveDateTime) -> Self {
        let (year, month, day, h, m, s, n) = (
            i64::from(value.year()),
            u8::try_from(value.month()).unwrap(),
            u8::try_from(value.day()).unwrap(),
            u8::try_from(value.hour()).unwrap(),
            u8::try_from(value.minute()).unwrap(),
            u8::try_from(value.second()).unwrap(),
            value.nanosecond(),
        );
        Self::from_gregorian_date_time(year, month, day, h, m, s, n)
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "chrono")]
    use chrono::{Duration as ChronoDuration, FixedOffset, TimeZone};
    use rstest::rstest;
    use rstest_reuse::{apply, template};
    #[cfg(feature = "time")]
    use time::{macros::datetime, Date as TimeDate, Time as TimeTime, UtcOffset};

    use super::*;

    #[rstest]
    #[case::jd_minus_one((-4713, 11, 23), -1)]
    #[case::jd_day_zero((-4713, 11, 24), 0)]
    #[case::jd_year_one((-4712, 1, 1), 38)]
    #[case::first_day_of_one_bc((0, 1, 1), 1_721_060)]
    #[case::year_zero_leap((0, 2, 29), 1_721_119)]
    #[case::third_month_day_one((0, 3, 1), 1_721_120)]
    #[case::last_day_in_year_zero((0, 12, 31), 1_721_425)]
    #[case::year_one_first_day((1, 1, 1), 1_721_426)]
    #[case::unix_timestamp((1970, 1, 1), 2_440_588)]
    #[case::end_of_year((1979, 12, 31), 2_444_239)]
    #[case::end_of_year_plus_one((1980, 1, 1), 2_444_240)]
    #[case::month_is_12((0, 12, 1), 1_721_395)]
    #[case::day_is_31_when_month_has_31((1, 12, 31), 1_721_790)]
    #[case::day_is_31_when_month_has_30((1, 11, 31), 1_721_760)]
    #[case::day_is_31_when_month_has_28((1971, 2, 31), 2_441_014)]
    #[case::day_is_31_when_month_has_29((1972, 2, 31), 2_441_379)]
    #[case::around_min_possible_year(
        ((i64::MIN) / 366, 1, 1),
        -9_204_282_680_793_170_880
    )]
    #[case::around_max_possible_year(
        ((i64::MAX - 31 - 337 - 1_721_119) / 366, 12, 31),
        9_204_282_680_794_895_265
    )]
    fn test_julian_days_from_gregorian(#[case] ymd: (i64, u8, u8), #[case] expected: i64) {
        assert_eq!(
            JulianDay::from_gregorian(ymd.0, ymd.1, ymd.2),
            JulianDay(expected)
        );
    }

    #[template]
    #[rstest]
    #[case::max_year((i64::MAX, 1, 1))]
    #[case::min_year((i64::MIN, 1, 1))]
    #[case::min_year_march((i64::MIN, 3, 1))]
    #[case::around_min_possible_year(
        ((i64::MIN) / 365, 1, 1),
    )]
    #[case::around_max_possible_year(
        ((i64::MAX - 31 - 337 - 1_721_119) / 365, 12, 31),
    )]
    fn test_julian_days_from_gregorian_error_template(#[case] ymd: (i64, u8, u8)) {}

    #[should_panic]
    #[apply(test_julian_days_from_gregorian_error_template)]
    fn test_julian_days_from_gregorian_then_panic(ymd: (i64, u8, u8)) {
        JulianDay::from_gregorian(ymd.0, ymd.1, ymd.2);
    }

    #[apply(test_julian_days_from_gregorian_error_template)]
    fn test_julian_days_try_from_gregorian_then_none(ymd: (i64, u8, u8)) {
        assert_eq!(JulianDay::try_from_gregorian(ymd.0, ymd.1, ymd.2), None);
    }

    #[rstest]
    #[case::illegal_month_too_low((0, 0, 1))]
    #[case::illegal_month_too_high((0, 13, 1))]
    #[case::illegal_day_too_low((0, 1, 0))]
    #[case::illegal_day_too_high((0, 1, 32))]
    #[should_panic]
    fn test_julian_days_try_from_gregorian_with_illegal_argument_then_panic(
        #[case] ymd: (i64, u8, u8),
    ) {
        JulianDay::try_from_gregorian(ymd.0, ymd.1, ymd.2);
    }

    #[test]
    fn test_julian_days_as_days() {
        assert_eq!(JulianDay(1).as_days(), 1);
    }

    #[test]
    #[cfg_attr(miri, ignore)] // test takes too long with miri
    fn test_julian_days_from_and_to_gregorian_brute_force_2000() {
        for y in -2000..2000 {
            for m in 1..=12 {
                for d in 1..=28 {
                    let jd = JulianDay::from_gregorian(y, m, d);
                    assert_eq!(jd.to_gregorian().unwrap(), (y, m, d));
                }
            }
        }
    }

    #[rstest]
    #[case::barely_below_max_possible(i64::MAX / 101, (250_027_078_488_026, 1, 22))]
    fn test_julian_days_to_gregorian(#[case] jd: i64, #[case] expected: (i64, u8, u8)) {
        assert_eq!(JulianDay(jd).to_gregorian(), Some(expected));
    }

    #[rstest]
    #[case::min(i64::MIN)]
    #[case::max(i64::MAX)]
    #[case::barely_above_max_possible(i64::MAX / 100)]
    fn test_julian_days_to_gregorian_then_none(#[case] jd: i64) {
        assert_eq!(JulianDay(jd).to_gregorian(), None);
    }

    #[template]
    #[rstest]
    #[case::zero(0, 0, 0)]
    #[case::one(0, 1, 1)]
    #[case::minus_one(0, -1, -1)]
    #[case::one_zero(1, 0, 1)]
    #[case::one_one(1, 1, 2)]
    #[case::minus_one_one(-1, -1, -2)]
    #[case::min(i64::MIN, 0, i64::MIN)]
    #[case::max(0, i64::MAX, i64::MAX)]
    #[case::min_plus_max(i64::MIN, i64::MAX, -1)]
    fn test_julian_days_arithmetic_template(
        #[case] lhs: i64,
        #[case] rhs: i64,
        #[case] expected: i64,
    ) {
    }

    #[apply(test_julian_days_arithmetic_template)]
    fn test_julian_days_checked_add(lhs: i64, rhs: i64, expected: i64) {
        assert_eq!(
            JulianDay(lhs).checked_add(JulianDay(rhs)),
            Some(JulianDay(expected))
        );
        assert_eq!(
            JulianDay(rhs).checked_add(JulianDay(lhs)),
            Some(JulianDay(expected))
        );
    }

    #[rstest]
    #[case::one(1, i64::MAX)]
    #[case::minus_one(-1, i64::MIN)]
    fn test_julian_days_checked_add_then_none(#[case] jd: i64, #[case] add: i64) {
        assert_eq!(JulianDay(jd).checked_add(JulianDay(add)), None);
    }

    #[apply(test_julian_days_arithmetic_template)]
    fn test_julian_days_checked_sub(lhs: i64, rhs: i64, expected: i64) {
        assert_eq!(
            JulianDay(lhs).checked_sub(JulianDay(-rhs)),
            Some(JulianDay(expected))
        );
    }

    #[test]
    fn test_julian_days_checked_sub_then_none() {
        assert_eq!(JulianDay(i64::MIN).checked_sub(JulianDay(1)), None);
    }

    #[apply(test_julian_days_arithmetic_template)]
    fn test_julian_days_checked_add_days(lhs: i64, rhs: i64, expected: i64) {
        assert_eq!(
            JulianDay(lhs).checked_add_days(rhs),
            Some(JulianDay(expected))
        );
        assert_eq!(
            JulianDay(rhs).checked_add_days(lhs),
            Some(JulianDay(expected))
        );
    }

    #[test]
    fn test_julian_checked_add_days_then_none() {
        assert_eq!(JulianDay(i64::MAX).checked_add_days(1), None);
    }

    #[apply(test_julian_days_arithmetic_template)]
    fn test_julian_days_checked_sub_days(lhs: i64, rhs: i64, expected: i64) {
        assert_eq!(
            JulianDay(lhs).checked_sub_days(-rhs),
            Some(JulianDay(expected))
        );
    }

    #[test]
    fn test_julian_days_checked_sub_days_then_none() {
        assert_eq!(JulianDay(i64::MIN).checked_sub_days(1), None);
    }

    #[rstest]
    #[case::some(
        (0, 1, 1, 23, 59, 59, 0),
        JulianDay(1_721_060),
        86399 * 1_000_000_000
    )]
    fn test_date_time_from_gregorian_date_time(
        #[case] date_time: (i64, u8, u8, u8, u8, u8, u32),
        #[case] expected_days: JulianDay,
        #[case] expected_time: u64,
    ) {
        let actual = DateTime::from_gregorian_date_time(
            date_time.0,
            date_time.1,
            date_time.2,
            date_time.3,
            date_time.4,
            date_time.5,
            date_time.6,
        );
        let expected = DateTime {
            days: expected_days,
            time: expected_time,
        };
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_date_time_to_gregorian_date() {
        let date_time = DateTime::UNIX_EPOCH;
        assert_eq!(date_time.to_gregorian_date(), Some((1970, 1, 1)));
    }

    #[test]
    fn test_date_time_to_gregorian_date_time() {
        let date_time = DateTime::UNIX_EPOCH;
        assert_eq!(
            date_time.to_gregorian_date_time(),
            Some((1970, 1, 1, 0, 0, 0, 0))
        );
    }

    #[test]
    fn test_date_time_as_julian_day() {
        let date_time = DateTime::UNIX_EPOCH;
        assert_eq!(date_time.as_julian_day(), JulianDay(2_440_588));
    }

    #[rstest]
    #[case::min((0, 0, 0, 0))]
    #[case::one_nano((0, 0, 0, 1))]
    #[case::one_sec((0, 0, 1, 0))]
    #[case::one_min((0, 1, 0, 0))]
    #[case::one_hour((1, 0, 0, 0))]
    #[case::all_one((1, 1, 1, 1))]
    #[case::max((23, 59, 59, 999_999_999))]
    fn test_date_time_as_hmsn(#[case] hmsn: (u8, u8, u8, u32)) {
        assert_eq!(
            DateTime::from_gregorian_date_time(1, 1, 1, hmsn.0, hmsn.1, hmsn.2, hmsn.3).as_hmsn(),
            hmsn
        );
    }

    #[template]
    #[rstest]
    #[case::zero(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        Duration::ZERO,
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0)
    )]
    #[case::max(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        Duration::MAX,
        DateTime::from_gregorian_date_time(584_554_051_223, 11, 9, 7, 0, 15, 999_999_999)
    )]
    #[case::min(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        Duration::MIN,
        DateTime::from_gregorian_date_time(-584_554_047_284, 2, 23, 16, 59, 44, 1)
    )]
    #[case::leap_year_plus_something(
        DateTime::from_gregorian_date_time(1972, 1, 1, 0, 0, 0, 0),
        Duration::positive(100 * 60 * 60, 0),
        DateTime::from_gregorian_date_time(1972, 1, 5, 4, 0, 0, 0)
    )]
    #[case::leap_year_plus_days_until_end_of_feb(
        DateTime::from_gregorian_date_time(1972, 1, 1, 0, 0, 0, 0),
        Duration::positive(86400 * (29 + 30), 0),
        DateTime::from_gregorian_date_time(1972, 2, 29, 0, 0, 0, 0)
    )]
    #[case::with_high_hms(
        DateTime::from_gregorian_date_time(1972, 1, 1, 23, 59, 59, 999_999_999),
        Duration::positive(86399, 999_999_999),
        DateTime::from_gregorian_date_time(1972, 1, 2, 23, 59, 59, 999_999_998)
    )]
    #[case::nano_second(
        DateTime::from_gregorian_date_time(1972, 1, 1, 23, 59, 59, 999_999_999),
        Duration::positive(0, 1),
        DateTime::from_gregorian_date_time(1972, 1, 2, 0, 0, 0, 0)
    )]
    #[case::nano_second_year_overflow(
        DateTime::from_gregorian_date_time(1969, 12, 31, 23, 59, 59, 999_999_999),
        Duration::positive(0, 1),
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0)
    )]
    #[case::day_year_overflow(
        DateTime::from_gregorian_date_time(1969, 12, 31, 23, 59, 59, 999_999_999),
        Duration::positive(86400, 0),
        DateTime::from_gregorian_date_time(1970, 1, 1, 23, 59, 59, 999_999_999)
    )]
    #[case::day_and_nano_year_overflow(
        DateTime::from_gregorian_date_time(1969, 12, 30, 23, 59, 59, 999_999_999),
        Duration::positive(86400, 1),
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0)
    )]
    #[case::negative_nano_second(
        DateTime::from_gregorian_date_time(1972, 1, 1, 0, 0, 0, 0),
        Duration::negative(0, 1),
        DateTime::from_gregorian_date_time(1971, 12, 31, 23, 59, 59, 999_999_999)
    )]
    #[case::negative_nano_second_year_overflow(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        Duration::negative(0, 1),
        DateTime::from_gregorian_date_time(1969, 12, 31, 23, 59, 59, 999_999_999)
    )]
    #[case::negative_day(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        Duration::negative(86400, 0),
        DateTime::from_gregorian_date_time(1969, 12, 31, 0, 0, 0, 0)
    )]
    #[case::negative_day_and_nano(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        Duration::negative(86400, 1),
        DateTime::from_gregorian_date_time(1969, 12, 30, 23, 59, 59, 999_999_999)
    )]
    fn test_date_time_checked_add_sub_duration_template(
        #[case] datetime: DateTime,
        #[case] duration: Duration,
        #[case] expected: DateTime,
    ) {
    }

    #[apply(test_date_time_checked_add_sub_duration_template)]
    fn test_date_time_checked_add_duration(
        datetime: DateTime,
        duration: Duration,
        expected: DateTime,
    ) {
        let new = datetime.checked_add_duration(&duration).unwrap();
        assert_eq!(
            new,
            expected,
            "as gregorian: {:?} {:?}",
            new.to_gregorian_date(),
            new.as_hmsn()
        );
    }

    #[apply(test_date_time_checked_add_sub_duration_template)]
    fn test_date_time_checked_sub_duration(
        expected: DateTime,
        duration: Duration,
        datetime: DateTime,
    ) {
        let new = datetime.checked_sub_duration(&duration).unwrap();
        assert_eq!(
            new,
            expected,
            "as gregorian: {:?} {:?}",
            new.to_gregorian_date(),
            new.as_hmsn()
        );
    }

    #[rstest]
    #[case::zero(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (0, 0, 0),
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
    )]
    #[case::one_year(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (1, 0, 0),
        DateTime::from_gregorian_date_time(1971, 1, 1, 0, 0, 0, 0),
    )]
    #[case::one_month(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (0, 1, 0),
        DateTime::from_gregorian_date_time(1970, 2, 1, 0, 0, 0, 0),
    )]
    #[case::one_day(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (0, 0, 1),
        DateTime::from_gregorian_date_time(1970, 1, 2, 0, 0, 0, 0),
    )]
    #[case::all_one(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (1, 1, 1),
        DateTime::from_gregorian_date_time(1971, 2, 2, 0, 0, 0, 0),
    )]
    #[case::minus_one_year(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (-1, 0, 0),
        DateTime::from_gregorian_date_time(1969, 1, 1, 0, 0, 0, 0),
    )]
    #[case::minus_one_month(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (0, -1, 0),
        DateTime::from_gregorian_date_time(1969, 12, 1, 0, 0, 0, 0),
    )]
    #[case::minus_one_day(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (0, 0, -1),
        DateTime::from_gregorian_date_time(1969, 12, 31, 0, 0, 0, 0),
    )]
    #[case::all_minus_one(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        (-1, -1, -1),
        DateTime::from_gregorian_date_time(1968, 11, 30, 0, 0, 0, 0),
    )]
    #[case::month_overflow(
        DateTime::from_gregorian_date_time(1970, 12, 1, 0, 0, 0, 0),
        (0, 11, 0),
        DateTime::from_gregorian_date_time(1971, 11, 1, 0, 0, 0, 0),
    )]
    #[case::month(
        DateTime::from_gregorian_date_time(1972, 2, 1, 0, 0, 0, 0),
        (0, 1, 0),
        DateTime::from_gregorian_date_time(1972, 3, 1, 0, 0, 0, 0),
    )]
    fn test_date_time_checked_add_gregorian(
        #[case] datetime: DateTime,
        #[case] ymd: (i64, i64, i64),
        #[case] expected: DateTime,
    ) {
        assert_eq!(
            datetime.checked_add_gregorian(ymd.0, ymd.1, ymd.2),
            Some(expected)
        );
    }

    #[rstest]
    #[case::max_years(
        DateTime::from_gregorian_date_time(-4713, 11, 24, 0, 0, 0, 0),
        (i64::MAX, 0, 0),
    )]
    #[case::min_years(
        DateTime::from_gregorian_date_time(-4713, 11, 24, 0, 0, 0, 0),
        (i64::MIN, 0, 0),
    )]
    fn test_date_time_checked_add_gregorian_then_none(
        #[case] datetime: DateTime,
        #[case] ymd: (i64, i64, i64),
    ) {
        assert_eq!(datetime.checked_add_gregorian(ymd.0, ymd.1, ymd.2), None);
    }

    #[rstest]
    #[case::one_nano(
        DateTime::from_gregorian_date_time(1970, 1, 2, 0, 0, 0, 2),
        DateTime::from_gregorian_date_time(1970, 1, 2, 0, 0, 0, 1),
        Duration::positive(0, 1)
    )]
    #[case::one_nano_when_year_overflow(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        DateTime::from_gregorian_date_time(1969, 12, 31, 23, 59, 59, 999_999_999),
        Duration::positive(0, 1)
    )]
    #[case::one_month_year_overflow(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        DateTime::from_gregorian_date_time(1969, 12, 1, 0, 0, 0, 0),
        Duration::positive(86400 * 31, 0)
    )]
    #[case::one_nano_negative(
        DateTime::from_gregorian_date_time(1970, 1, 2, 23, 59, 59, 0),
        DateTime::from_gregorian_date_time(1970, 1, 2, 23, 59, 59, 1),
        Duration::negative(0, 1)
    )]
    #[case::one_nano_negative(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 1),
        Duration::negative(0, 1)
    )]
    #[case::one_day_negative(
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0),
        DateTime::from_gregorian_date_time(1970, 1, 2, 0, 0, 0, 0),
        Duration::negative(86400, 0)
    )]
    fn test_date_time_checked_sub(
        #[case] datetime: DateTime,
        #[case] rhs: DateTime,
        #[case] expected: Duration,
    ) {
        assert_eq!(datetime.duration_since(rhs), Some(expected));
    }

    // SystemTime is not accurate on windows targets and results sometimes differ by 1 nano second
    #[cfg(not(target_os = "windows"))]
    #[rstest]
    #[case::unix_epoch(SystemTime::UNIX_EPOCH, DateTime::UNIX_EPOCH)]
    #[case::second_before_unix_epoch(
        SystemTime::UNIX_EPOCH - StdDuration::new(1, 0),
        DateTime::from_gregorian_date_time(1969, 12, 31, 23, 59, 59, 0)
    )]
    #[case::nano_before_unix_epoch(
        SystemTime::UNIX_EPOCH - StdDuration::new(0, 1),
        DateTime::from_gregorian_date_time(1969, 12, 31, 23, 59, 59, 999_999_999)
    )]
    #[case::second_and_nano_before_unix_epoch(
        SystemTime::UNIX_EPOCH - StdDuration::new(1, 1),
        DateTime::from_gregorian_date_time(1969, 12, 31, 23, 59, 58, 999_999_999)
    )]
    #[case::second_after_unix_epoch(
        SystemTime::UNIX_EPOCH + StdDuration::new(1, 0),
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 1, 0)
    )]
    #[case::nano_after_unix_epoch(
        SystemTime::UNIX_EPOCH + StdDuration::new(0, 1),
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 1)
    )]
    #[case::second_and_nano_after_unix_epoch(
        SystemTime::UNIX_EPOCH + StdDuration::new(1, 1),
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 1, 1)
    )]
    fn test_date_time_now_utc(#[case] now: SystemTime, #[case] expected: DateTime) {
        assert_eq!(DateTime::now_utc_with_system_time(now), expected);
    }

    #[test]
    fn test_date_time_now_utc_calls_now() {
        assert_eq!(DateTime::now_utc(), DateTime::UNIX_EPOCH);
    }

    #[test]
    fn test_ordinal_to_month_lookup_table() {
        let mut ordinal = 0usize;
        for m in 0..=11usize {
            let days_of_month: usize =
                // m == 0 is March
                if m == 0 || m == 2 || m == 4 || m == 5 || m == 7 || m == 9 || m == 10 {
                    31
                } else if m == 1 || m == 3 || m == 6 || m == 8 {
                    30
                } else {
                    29
                };
            for _ in 1..=days_of_month {
                assert_eq!(
                    ORDINAL_TO_MONTH[ordinal],
                    u8::try_from((m + 2) % 12 + 1).unwrap()
                );
                ordinal += 1;
            }
        }
    }

    #[cfg(any(feature = "time", feature = "chrono"))]
    #[template]
    #[rstest]
    #[case::year_zero(
        (0i32, 1, 1, 0, 0, 0, 0, 0i32),
        DateTime::from_gregorian_date_time(0, 1, 1, 0, 0, 0, 0)
    )]
    #[case::positive_offset(
        (0i32, 1, 1, 0, 0, 0, 0, 2i32 * 3600i32),
        DateTime::from_gregorian_date_time(0, 1, 1, 2, 0, 0, 0)
    )]
    #[case::max_positive_offset(
        (0i32, 1, 1, 0, 0, 0, 0, 86399i32),
        DateTime::from_gregorian_date_time(0, 1, 1, 23, 59, 59, 0)
    )]
    #[case::negative_offset(
        (0i32, 1, 1, 0, 0, 0, 0, -2i32 * 3600i32),
        DateTime::from_gregorian_date_time(-1, 12, 31, 22, 0, 0, 0)
    )]
    #[case::max_negative_offset(
        (0i32, 1, 1, 0, 0, 0, 0, -86399i32),
        DateTime::from_gregorian_date_time(-1, 12, 31, 0, 0, 1, 0)
    )]
    #[case::unix_epoch(
        (1970i32, 1, 1, 0, 0, 0, 0, 0i32),
        DateTime::from_gregorian_date_time(1970, 1, 1, 0, 0, 0, 0)
    )]
    #[case::some_positive_year(
        (1453i32, 6, 23, 14, 57, 29, 123456789, 0i32),
        DateTime::from_gregorian_date_time(1453, 6, 23, 14, 57, 29, 123_456_789),
    )]
    #[case::some_negative_year(
        (-1453i32, 6, 23, 14, 57, 29, 123456789, 0i32),
        DateTime::from_gregorian_date_time(-1453, 6, 23, 14, 57, 29, 123_456_789),
    )]
    fn test_into_date_time_template(
        #[case] ymdhmsno: (i32, u8, u8, u8, u8, u8, u32, i32),
        #[case] date_time: DateTime,
    ) {
    }

    #[cfg(feature = "time")]
    #[apply(test_into_date_time_template)]
    fn test_time_offset_date_time_into_date_time(
        ymdhmsno: (i32, u8, u8, u8, u8, u8, u32, i32),
        date_time: DateTime,
    ) {
        let offset_date = PrimitiveDateTime::new(
            TimeDate::from_calendar_date(ymdhmsno.0, ymdhmsno.1.try_into().unwrap(), ymdhmsno.2)
                .unwrap(),
            TimeTime::from_hms_nano(ymdhmsno.3, ymdhmsno.4, ymdhmsno.5, ymdhmsno.6).unwrap(),
        )
        .assume_utc()
        .to_offset(UtcOffset::from_whole_seconds(ymdhmsno.7).unwrap());
        assert_eq!(DateTime::from(offset_date), date_time);
    }

    #[cfg(feature = "time")]
    #[rstest]
    #[case::max(999_999i32)]
    #[case::min(-999_999i32)]
    fn test_time_offset_date_time_min_max_into_date_time(#[case] year: i32) {
        let offset_date = PrimitiveDateTime::new(
            TimeDate::from_calendar_date(year, 12.try_into().unwrap(), 31).unwrap(),
            TimeTime::from_hms_nano(23, 59, 59, 999_999_999).unwrap(),
        )
        .assume_utc();
        assert_eq!(
            DateTime::from(offset_date),
            DateTime::from_gregorian_date_time(
                year.try_into().unwrap(),
                12,
                31,
                23,
                59,
                59,
                999_999_999
            )
        );
    }

    #[cfg(feature = "time")]
    #[test]
    fn test_time_primitive_date_time_into_date_time() {
        assert_eq!(
            DateTime::from(datetime!(0-1-1 00:00:00)),
            DateTime::from_gregorian_date_time(0, 1, 1, 0, 0, 0, 0)
        );
    }

    #[cfg(feature = "chrono")]
    #[apply(test_into_date_time_template)]
    fn test_chrono_date_time_into_date_time(
        #[case] ymdhmsno: (i32, u8, u8, u8, u8, u8, u32, i32),
        #[case] date_time: DateTime,
    ) {
        let mut chrono_date = FixedOffset::west_opt(ymdhmsno.7)
            .unwrap()
            .with_ymd_and_hms(
                ymdhmsno.0,
                ymdhmsno.1.try_into().unwrap(),
                ymdhmsno.2.try_into().unwrap(),
                ymdhmsno.3.try_into().unwrap(),
                ymdhmsno.4.try_into().unwrap(),
                ymdhmsno.5.try_into().unwrap(),
            )
            .unwrap();
        chrono_date += ChronoDuration::nanoseconds(ymdhmsno.6.try_into().unwrap());
        assert_eq!(DateTime::from(chrono_date), date_time);
    }

    #[cfg(feature = "chrono")]
    #[rstest]
    #[case::max(i32::MAX >> 13i32)]
    #[case::min(i32::MIN >> 13i32)]
    fn test_chrono_date_time_min_max_into_date_time(#[case] year: i32) {
        let mut chrono_date = FixedOffset::west_opt(0)
            .unwrap()
            .with_ymd_and_hms(year, 12, 31, 23, 59, 59)
            .unwrap();
        chrono_date += ChronoDuration::nanoseconds(999_999_999);
        assert_eq!(
            DateTime::from(chrono_date),
            DateTime::from_gregorian_date_time(year.into(), 12, 31, 23, 59, 59, 999_999_999)
        );
    }
}
