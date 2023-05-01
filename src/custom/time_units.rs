// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use crate::time::TimeUnitsLike;
use crate::TimeUnit::*;
use crate::{
    Multiplier, TimeUnit, DEFAULT_ID_DAY, DEFAULT_ID_HOUR, DEFAULT_ID_MICRO_SECOND,
    DEFAULT_ID_MILLI_SECOND, DEFAULT_ID_MINUTE, DEFAULT_ID_MONTH, DEFAULT_ID_NANO_SECOND,
    DEFAULT_ID_SECOND, DEFAULT_ID_WEEK, DEFAULT_ID_YEAR,
};

/// The [`Identifiers`] as defined in
/// [`systemd.time`](https://www.man7.org/linux/man-pages/man7/systemd.time.7.html)
pub const SYSTEMD_TIME_UNITS: [(TimeUnit, &[&str]); 10] = [
    (NanoSecond, &["ns", "nsec"]),
    (MicroSecond, &["us", "µs", "usec"]),
    (MilliSecond, &["ms", "msec"]),
    (Second, &["s", "sec", "second", "seconds"]),
    (Minute, &["m", "min", "minute", "minutes"]),
    (Hour, &["h", "hr", "hour", "hours"]),
    (Day, &["d", "day", "days"]),
    (Week, &["w", "week", "weeks"]),
    (Month, &["M", "month", "months"]),
    (Year, &["y", "year", "years"]),
];

/// The default [`Identifiers`] token from the `standard` feature (without `Month` and `Year`)
pub const DEFAULT_TIME_UNITS: [(TimeUnit, &[&str]); 8] = [
    (NanoSecond, &[DEFAULT_ID_NANO_SECOND]),
    (MicroSecond, &[DEFAULT_ID_MICRO_SECOND]),
    (MilliSecond, &[DEFAULT_ID_MILLI_SECOND]),
    (Second, &[DEFAULT_ID_SECOND]),
    (Minute, &[DEFAULT_ID_MINUTE]),
    (Hour, &[DEFAULT_ID_HOUR]),
    (Day, &[DEFAULT_ID_DAY]),
    (Week, &[DEFAULT_ID_WEEK]),
];

/// All [`Identifiers`] token from the `standard` feature (with `Month` and `Year`)
pub const DEFAULT_ALL_TIME_UNITS: [(TimeUnit, &[&str]); 10] = [
    (NanoSecond, &[DEFAULT_ID_NANO_SECOND]),
    (MicroSecond, &[DEFAULT_ID_MICRO_SECOND]),
    (MilliSecond, &[DEFAULT_ID_MILLI_SECOND]),
    (Second, &[DEFAULT_ID_SECOND]),
    (Minute, &[DEFAULT_ID_MINUTE]),
    (Hour, &[DEFAULT_ID_HOUR]),
    (Day, &[DEFAULT_ID_DAY]),
    (Week, &[DEFAULT_ID_WEEK]),
    (Month, &[DEFAULT_ID_MONTH]),
    (Year, &[DEFAULT_ID_YEAR]),
];

pub(super) type IdentifiersLookupData<'a> = (LookupData, Vec<&'a str>);

/// A pair consisting of a [`TimeUnit`] and its associated identifiers
pub type Identifiers<'a> = (TimeUnit, &'a [&'a str]);

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(super) struct LookupData {
    min_length: usize,
    max_length: usize,
    time_unit: TimeUnit,
    multiplier: Multiplier,
}

impl LookupData {
    fn new(time_unit: TimeUnit, multiplier: Multiplier) -> Self {
        Self {
            min_length: usize::MAX,
            max_length: 0,
            time_unit,
            multiplier,
        }
    }

    fn update(&mut self, identifier: &str) {
        let len = identifier.len();
        if self.min_length > len {
            self.min_length = len;
        }
        if self.max_length < len {
            self.max_length = len;
        }
    }

    fn check(&self, identifier: &str) -> bool {
        let len = identifier.len();
        self.min_length <= len && self.max_length >= len
    }
}

/// A [`CustomTimeUnit`] is a completely customizable [`TimeUnit`] using an additional
/// [`Multiplier`].
///
/// Custom time units have a base [`TimeUnit`] (which has an inherent [`Multiplier`]) and an
/// optional [`Multiplier`] which acts as an additional [`Multiplier`] to the multiplier of the
/// `base_unit`. Using a multiplier with `Multiplier(1, 0)` is equivalent to using no multiplier at
/// all but see also the `Problems` section. A [`CustomTimeUnit`] also consists of identifiers which
/// are used to identify the [`CustomTimeUnit`] during the parsing process.
///
/// To create a [`CustomTimeUnit`] representing two weeks there are multiple solutions. Just to show
/// two very obvious examples:
///
/// ```rust
/// use fundu::TimeUnit::*;
/// use fundu::{CustomTimeUnit, Multiplier};
///
/// assert_ne!(
///     (CustomTimeUnit::new(Week, &["fortnight", "fortnights"], Some(Multiplier(2, 0)))),
///     (CustomTimeUnit::new(Day, &["fortnight", "fortnights"], Some(Multiplier(14, 0))))
/// );
/// ```
///
/// Both would actually be equal in the sense, that they would resolve to the same result when
/// multiplying the `base_unit` with the `multiplier`, however they are treated as not equal and
/// it's possible to choose freely between the definitions. Using both of the definitions in
/// parallel within the [`crate::CustomDurationParser`] would be possible and produces the desired
/// result, although it does not provide any benefits.
///
/// ```rust
/// use std::time::Duration;
///
/// use fundu::TimeUnit::*;
/// use fundu::{CustomDurationParser, CustomTimeUnit, Multiplier};
///
/// let parser = CustomDurationParser::builder()
///     .custom_time_units(&[
///         CustomTimeUnit::new(Week, &["fortnight", "fortnights"], Some(Multiplier(2, 0))),
///         CustomTimeUnit::new(Day, &["fortnight", "fortnights"], Some(Multiplier(14, 0))),
///     ])
///     .build();
///
/// assert_eq!(
///     parser.parse("1fortnight").unwrap(),
///     Duration::new(1209600, 0)
/// );
/// ```
///
/// In summary, the best choice is to use the [`CustomTimeUnit`] with a `base_unit` having the
/// lowest [`Multiplier`] but see also `Problems` below.
///
/// Equality of two [`CustomTimeUnit`] is defined as
///
/// ```ignore
/// base_unit == other.base_unit && multiplier == other.multiplier
/// ```
///
/// # Problems
///
/// For `base_unit`s other than `Second` there may occur an overflow (and panic) during the parsing
/// process.  The Multiplier boundaries are chosen as high as possible but if the `base_unit`
/// multiplier multiplied with `multiplier` exceeds `(u64::MAX, i16::MIN)` or `(u64::MAX, i16::MAX)`
/// this multiplication overflows. By example, with `Multiplier(m, e)` two multipliers x, y are
/// multiplied as follows : `m = x.m * y.m, e = x.e + y.e`:
///
/// If the `base_unit` is `Year`, which has a multiplier of `m = 31557600, e = 0`, then this
/// restricts the `multiplier` to `m = u64::MAX / 31557600 = 584_542_046_090, e = 32767 or e =
/// -32768`.
///
/// If the `base_unit` is `NanoSecond`, which has a multiplier of `m = 1, e = -9`, then this
/// restricts the `multiplier` to `m = u64::MAX, e = -32768 + 9 = -32,759 or e = i16::MAX = 32767`.
///
/// The `base_unit`s are `Second`s based what results in the following table with limits for the
/// `multiplier`:
///
/// | `base_unit`    | [`Multiplier`] | Limit m | Limit -e | Limit +e
/// | --------------- | ----------:| -------:| --------:| ------:|
/// | Nanosecond  | Multiplier(1, -9) | u64::MAX | -32,759 | i16::MAX
/// | Microsecond | Multiplier(1, -6) | u64::MAX | -32,762 | i16::MAX
/// | Millisecond | Multiplier(1, -3) | u64::MAX | -32,765 | i16::MAX
/// | Second      | Multiplier(1, 0) | u64::MAX | i16::MIN | i16::MAX
/// | Minute      | Multiplier(60, 0) | 307_445_734_561_825_860 | i16::MIN | i16::MAX
/// | Hour        | Multiplier(3600, 0) | 5_124_095_576_030_431 | i16::MIN | i16::MAX
/// | Day         | Multiplier(86400, 0) | 213_503_982_334_601 | i16::MIN | i16::MAX
/// | Week        | Multiplier(604800, 0) | 30_500_568_904_943  | i16::MIN | i16::MAX
/// | Month       | Multiplier(2629800, 0) | 7_014_504_553_087 | i16::MIN | i16::MAX
/// | Year        | Multiplier(31557600, 0) | 584_542_046_090 | i16::MIN | i16::MAX
#[derive(Debug, Eq, Clone, Copy)]
pub struct CustomTimeUnit<'a> {
    base_unit: TimeUnit,
    multiplier: Multiplier,
    identifiers: &'a [&'a str],
}

impl<'a> PartialEq for CustomTimeUnit<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.base_unit == other.base_unit && self.multiplier == other.multiplier
    }
}

impl<'a> CustomTimeUnit<'a> {
    /// Create a new [`CustomTimeUnit`]
    ///
    /// See also the documentation for [`CustomTimeUnit`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::time::Duration;
    ///
    /// use fundu::TimeUnit::*;
    /// use fundu::{CustomDurationParser, CustomTimeUnit, Multiplier};
    ///
    /// let time_unit = CustomTimeUnit::new(Second, &["shake", "shakes"], Some(Multiplier(1, -8)));
    /// let parser = CustomDurationParser::builder()
    ///     .custom_time_unit(time_unit)
    ///     .build();
    ///
    /// assert_eq!(parser.parse("1shake").unwrap(), Duration::new(0, 10));
    /// ```
    pub const fn new(
        base_unit: TimeUnit,
        identifiers: &'a [&'a str],
        multiplier: Option<Multiplier>,
    ) -> Self {
        Self {
            base_unit,
            multiplier: match multiplier {
                Some(m) => m,
                None => Multiplier(1, 0),
            },
            identifiers,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub(super) struct CustomTimeUnits<'a> {
    min_length: usize,
    max_length: usize,
    time_units: Vec<IdentifiersLookupData<'a>>,
}

impl<'a> CustomTimeUnits<'a> {
    pub(super) fn new() -> Self {
        Self::with_capacity(0)
    }

    pub(super) fn with_time_units(units: &[Identifiers<'a>]) -> Self {
        let mut time_units = Self::with_capacity(units.len());
        time_units.add_time_units(units);
        time_units
    }

    pub(super) fn with_capacity(capacity: usize) -> Self {
        Self {
            min_length: usize::MAX,
            max_length: 0,
            time_units: Vec::with_capacity(capacity),
        }
    }

    pub(super) fn add_time_unit(&mut self, unit: Identifiers<'a>) {
        let (time_unit, identifiers) = unit;
        self.add_custom_time_unit(CustomTimeUnit::new(time_unit, identifiers, None));
    }

    pub(super) fn add_time_units(&mut self, units: &[Identifiers<'a>]) {
        for unit in units {
            self.add_time_unit(*unit);
        }
    }

    pub(super) fn add_custom_time_unit(&mut self, time_unit: CustomTimeUnit<'a>) {
        if time_unit.identifiers.is_empty() {
            return;
        }
        let CustomTimeUnit {
            base_unit,
            multiplier,
            identifiers,
        } = time_unit;
        let (min_length, max_length) = match self.lookup_mut(base_unit, multiplier) {
            Some((data, ids)) => {
                for &identifier in identifiers.iter().filter(|&&id| !id.is_empty()) {
                    ids.push(identifier);
                    data.update(identifier);
                }
                (data.min_length, data.max_length)
            }
            None => {
                let mut data = LookupData::new(base_unit, multiplier);
                let mut ids = Vec::with_capacity(identifiers.len());
                for &identifier in identifiers.iter().filter(|&&id| !id.is_empty()) {
                    ids.push(identifier);
                    data.update(identifier);
                }
                if ids.is_empty() {
                    return;
                }
                let lengths = (data.min_length, data.max_length);
                self.time_units.push((data, ids));
                lengths
            }
        };
        self.update_lengths(min_length, max_length);
    }

    pub(super) fn lookup_mut(
        &'_ mut self,
        unit: TimeUnit,
        multiplier: Multiplier,
    ) -> Option<&'_ mut (LookupData, Vec<&'a str>)> {
        self.time_units
            .iter_mut()
            .find(|(data, _)| data.time_unit == unit && data.multiplier == multiplier)
    }

    #[allow(dead_code)]
    pub(super) fn lookup(
        &self,
        unit: TimeUnit,
        multiplier: Multiplier,
    ) -> Option<&(LookupData, Vec<&'a str>)> {
        self.time_units
            .iter()
            .find(|(data, _)| data.time_unit == unit && data.multiplier == multiplier)
    }

    pub(super) fn find_id(&self, id: &str) -> Option<(TimeUnit, Multiplier)> {
        self.time_units.iter().find_map(|(data, v)| {
            if data.check(id) && v.contains(&id) {
                Some((data.time_unit, data.multiplier))
            } else {
                None
            }
        })
    }

    pub(super) fn update_lengths(&mut self, min_length: usize, max_length: usize) {
        if self.min_length > min_length {
            self.min_length = min_length;
        }
        if self.max_length < max_length {
            self.max_length = max_length;
        }
    }
}

impl<'a> TimeUnitsLike for CustomTimeUnits<'a> {
    #[inline]
    fn is_empty(&self) -> bool {
        self.time_units.is_empty()
    }

    #[inline]
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        let len = identifier.len();
        if self.min_length > len || self.max_length < len {
            return None;
        }
        self.find_id(identifier)
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;

    fn make_lookup_result(
        min_length: usize,
        max_length: usize,
        time_unit: TimeUnit,
        multiplier: Multiplier,
        identifiers: Vec<&str>,
    ) -> (LookupData, Vec<&str>) {
        (
            LookupData {
                min_length,
                max_length,
                time_unit,
                multiplier,
            },
            identifiers,
        )
    }

    #[test]
    fn test_custom_time_units_init_new() {
        let custom = CustomTimeUnits::new();
        assert!(custom.time_units.is_empty());
        assert!(custom.is_empty());
    }

    #[rstest]
    #[case::nano_second(NanoSecond, &["some"], 4, 4)]
    #[case::nano_second_with_multiple_ids(NanoSecond, &["some", "other", "деякі"], 4, 10)]
    #[case::micro_second(MicroSecond, &["some"], 4, 4)]
    #[case::micro_second_with_multiple_ids(MicroSecond, &["some", "other", "деякі"], 4, 10)]
    #[case::milli_second(MilliSecond, &["some"], 4, 4)]
    #[case::milli_second_with_multiple_ids(MilliSecond, &["some", "other", "деякі"], 4, 10)]
    #[case::second(Second, &["some"], 4, 4)]
    #[case::second_with_multiple_ids(Second, &["some", "other", "деякі"], 4, 10)]
    #[case::minute(Minute, &["some"], 4, 4)]
    #[case::minute_with_multiple_ids(Minute, &["some", "other", "деякі"], 4, 10)]
    #[case::hour(Hour, &["some"], 4, 4)]
    #[case::hour_with_multiple_ids(Hour, &["some", "other", "деякі"], 4, 10)]
    #[case::day(Day, &["some"], 4, 4)]
    #[case::day_with_multiple_ids(Day, &["some", "other", "деякі"], 4, 10)]
    #[case::week(Week, &["some"], 4, 4)]
    #[case::week_with_multiple_ids(Week, &["some", "other", "деякі"], 4, 10)]
    #[case::month(Month, &["some"], 4, 4)]
    #[case::month_with_multiple_ids(Month, &["some", "other", "деякі"], 4, 10)]
    #[case::year(Year, &["some"], 4, 4)]
    #[case::year_with_multiple_ids(Year, &["some", "other", "деякі"], 4, 10)]
    fn test_custom_time_units_init_with_time_units(
        #[case] time_unit: TimeUnit,
        #[case] ids: &[&str],
        #[case] min_length: usize,
        #[case] max_length: usize,
    ) {
        let custom = CustomTimeUnits::with_time_units(&[(time_unit, ids)]);
        assert!(!custom.is_empty());
        assert_eq!(
            custom.lookup(time_unit, Multiplier::default()),
            Some(&make_lookup_result(
                min_length,
                max_length,
                time_unit,
                Multiplier::default(),
                Vec::from(ids)
            ))
        );
    }

    #[test]
    fn test_custom_time_units_init_with_time_units_when_multiple_equal_ids() {
        let custom = CustomTimeUnits::with_time_units(&[(NanoSecond, &["same", "same"])]);
        assert!(!custom.is_empty());
        assert_eq!(
            custom.lookup(NanoSecond, Multiplier::default()),
            Some(&make_lookup_result(
                4,
                4,
                NanoSecond,
                Multiplier::default(),
                vec!["same", "same"]
            ))
        );
        assert_eq!(
            custom.get("same"),
            Some((NanoSecond, Multiplier::default()))
        );
    }

    #[test]
    fn test_custom_time_units_when_add_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((MicroSecond, &["some", "ids"]));
        assert!(
            custom
                .time_units
                .iter()
                .filter(|(data, _)| data.time_unit != MicroSecond)
                .all(|(_, v)| v.is_empty())
        );
        assert_eq!(
            custom.lookup(MicroSecond, Multiplier::default()).unwrap().1,
            vec!["some", "ids"]
        );
        assert_eq!(
            custom.get("some"),
            Some((MicroSecond, Multiplier::default()))
        );
        assert_eq!(
            custom.get("ids"),
            Some((MicroSecond, Multiplier::default()))
        );
        assert_eq!(custom.get("does not exist"), None);
        assert!(!custom.is_empty());
    }

    #[test]
    fn test_custom_time_units_when_adding_time_unit_with_empty_slice_then_not_added() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((MicroSecond, &[]));
        assert!(custom.is_empty());
        assert_eq!(custom.lookup(MicroSecond, Multiplier::default()), None);
    }

    #[test]
    fn test_custom_time_units_when_adding_time_unit_with_empty_id_then_not_added() {
        let mut custom = CustomTimeUnits::new();
        custom.add_time_unit((MicroSecond, &[""]));
        assert!(custom.is_empty());
        assert_eq!(custom.lookup(MicroSecond, Multiplier::default()), None);
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_with_empty_id_then_not_added() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &[""], Some(Multiplier(2, 0))));
        assert!(custom.is_empty());
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(
            Second,
            &["sec"],
            Some(Multiplier(2, 0)),
        ));
        assert!(!custom.is_empty());
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                3,
                3,
                Second,
                Multiplier(2, 0),
                vec!["sec"]
            ))
        );
        assert_eq!(custom.get("sec"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_multiple_custom_time_unit() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(
            Second,
            &["sec"],
            Some(Multiplier(1, 0)),
        ));
        custom.add_custom_time_unit(CustomTimeUnit::new(
            Second,
            &["secs"],
            Some(Multiplier(2, 0)),
        ));
        assert_eq!(
            custom.lookup(Second, Multiplier::default()),
            Some(&make_lookup_result(
                3,
                3,
                Second,
                Multiplier::default(),
                vec!["sec"]
            ))
        );
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                4,
                4,
                Second,
                Multiplier(2, 0),
                vec!["secs"]
            ))
        );
        assert_eq!(custom.get("sec"), Some((Second, Multiplier(1, 0))));
        assert_eq!(custom.get("secs"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_normal_time_unit_already_exists() {
        let mut custom = CustomTimeUnits::with_time_units(&[(Second, &["s"])]);
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &["ss"], Some(Multiplier(2, 0))));
        assert_eq!(
            custom.lookup(Second, Multiplier::default()),
            Some(&make_lookup_result(
                1,
                1,
                Second,
                Multiplier::default(),
                vec!["s"]
            ))
        );
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                2,
                2,
                Second,
                Multiplier(2, 0),
                vec!["ss"]
            ))
        );
        assert_eq!(custom.get("s"), Some((Second, Multiplier(1, 0))));
        assert_eq!(custom.get("ss"), Some((Second, Multiplier(2, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_normal_time_unit_with_same_id() {
        let mut custom = CustomTimeUnits::with_time_units(&[(Second, &["s"])]);
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &["s"], Some(Multiplier(2, 0))));
        assert_eq!(
            custom.lookup(Second, Multiplier::default()),
            Some(&make_lookup_result(
                1,
                1,
                Second,
                Multiplier::default(),
                vec!["s"]
            ))
        );
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                1,
                1,
                Second,
                Multiplier(2, 0),
                vec!["s"]
            ))
        );
        assert_eq!(custom.get("s"), Some((Second, Multiplier(1, 0))));
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_identifiers_is_empty() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &[], Some(Multiplier(2, 0))));
        assert!(custom.is_empty());
        assert_eq!(custom.lookup(Second, Multiplier(2, 0)), None);
    }

    #[test]
    fn test_custom_time_units_adding_custom_time_unit_when_adding_same_unit_twice() {
        let mut custom = CustomTimeUnits::new();
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &["s"], Some(Multiplier(2, 0))));
        custom.add_custom_time_unit(CustomTimeUnit::new(Second, &["s"], Some(Multiplier(2, 0))));
        assert_eq!(
            custom.lookup(Second, Multiplier(2, 0)),
            Some(&make_lookup_result(
                1,
                1,
                Second,
                Multiplier(2, 0),
                vec!["s", "s"]
            ))
        );
    }

    #[rstest]
    #[case::none_and_default_multiplier_when_same_ids(CustomTimeUnit::new(Second, &["s"], None), CustomTimeUnit::new(Second, &["s"], Some(Multiplier::default())))]
    #[case::none_and_default_multiplier_when_different_ids(CustomTimeUnit::new(Second, &["s"], None), CustomTimeUnit::new(Second, &["secs"], Some(Multiplier::default())))]
    #[case::same_multipliers(CustomTimeUnit::new(Second, &["s"], Some(Multiplier(2,0))), CustomTimeUnit::new(Second, &["secs"], Some(Multiplier(2,0))))]
    fn test_custom_time_unit_equality_when_equal(
        #[case] time_unit: CustomTimeUnit,
        #[case] other: CustomTimeUnit,
    ) {
        assert_eq!(time_unit, other);
    }

    #[rstest]
    #[case::different_time_units(CustomTimeUnit::new(MilliSecond, &["ms"], Some(Multiplier(1,0))), CustomTimeUnit::new(Second, &["ms"], Some(Multiplier(1,0))))]
    #[case::different_multipliers(CustomTimeUnit::new(MilliSecond, &["ms"], Some(Multiplier(1000,0))), CustomTimeUnit::new(Second, &["ms"], Some(Multiplier(1,0))))]
    fn test_custom_time_unit_equality_when_not_equal(
        #[case] time_unit: CustomTimeUnit,
        #[case] other: CustomTimeUnit,
    ) {
        assert_ne!(time_unit, other);
    }
}
