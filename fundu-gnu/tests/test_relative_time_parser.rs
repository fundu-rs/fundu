// spell-checker: ignore secondss datetime agotomorrow
// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration as StdDuration;

use fundu_core::time::TimeUnit::*;
use fundu_core::time::{Multiplier, TimeUnit};
use fundu_gnu::{
    parse, parse_fuzzy, parse_with_date, DateTime, Duration, ParseError, RelativeTimeParser,
};
use rstest::rstest;
pub use rstest_reuse;
use rstest_reuse::{apply, template};
#[cfg(feature = "time")]
use time::{macros::datetime, OffsetDateTime, PrimitiveDateTime};

#[rstest]
#[case::zero("0", Duration::ZERO)]
#[case::minus_zero("-0", Duration::ZERO)]
#[case::just_number("1", Duration::positive(1, 0))]
#[case::number_with_plus_sign("+1", Duration::positive(1, 0))]
#[case::time_unit_without_number("sec", Duration::positive(1, 0))]
#[case::time_unit_with_plus_sign("+sec", Duration::positive(1, 0))]
#[case::time_unit_with_plus_sign_and_delim("+   sec", Duration::positive(1, 0))]
#[case::sign_with_all_whitespace("-\x09\x0A\x0B\x0C\x0D sec", Duration::negative(1, 0))]
#[case::number_with_whitespace_between_time_unit("1 sec", Duration::positive(1, 0))]
#[case::number_with_all_whitespace_between_time_unit(
    "1\x09\x0A\x0B\x0C\x0D sec",
    Duration::positive(1, 0)
)]
#[case::one_yesterday("1 yesterday", Duration::negative(24 * 60 * 60 - 1, 0))]
#[case::negative("-1", Duration::negative(1, 0))]
#[case::ago("1 sec ago", Duration::negative(1, 0))]
#[case::ago_with_all_whitespace("1 sec\x09\x0A\x0B\x0C\x0D ago", Duration::negative(1, 0))]
#[case::negative_with_ago("-1 sec ago", Duration::positive(1, 0))]
#[case::multiple("1 sec 1 sec", Duration::positive(2, 0))]
#[case::multiple_with_all_whitespace("1 sec\x09\x0A\x0B\x0C\x0D 1 sec", Duration::positive(2, 0))]
#[case::multiple_with_ago("1 sec ago 1 sec", Duration::ZERO)]
#[case::multiple_when_other_is_zero("1 sec 0 sec", Duration::positive(1, 0))]
#[case::multiple_when_plus_sign_as_delimiter("1 sec+1 sec", Duration::positive(2, 0))]
#[case::multiple_when_minus_sign_as_delimiter("3 sec-1 sec", Duration::positive(2, 0))]
#[case::arithmetic_like_expressions("3 sec - 1 sec", Duration::positive(2, 0))]
#[case::fraction_when_no_time_unit("1.1", Duration::positive(1, 100_000_000))]
#[case::fraction_when_second_time_unit("1.1sec", Duration::positive(1, 100_000_000))]
#[case::fraction_with_whole_zero("0.1", Duration::positive(0, 100_000_000))]
#[case::fraction_with_whole_zero_when_sec("0.1sec", Duration::positive(0, 100_000_000))]
#[case::fraction_with_fract_zero("1.0", Duration::positive(1, 0))]
#[case::fraction_with_fract_zero_when_sec("1.0sec", Duration::positive(1, 0))]
#[case::fraction_gets_capped("0.0123456789sec", Duration::positive(0, 12_345_678))]
#[case::positive_years_overflow("583344214028year", Duration::positive(18408565361559340800, 0))]
#[case::sec_two("sec2", Duration::positive(3, 0))]
fn test_parser_parse_valid_input(#[case] input: &str, #[case] expected: Duration) {
    assert_eq!(RelativeTimeParser::new().parse(input), Ok(expected));
    assert_eq!(parse(input), Ok(expected));
}

#[rstest]
#[case::fuzz(
    "+minute agotomorrow year",
    ParseError::InvalidInput("agotomorrow year".to_owned())
)]
#[case::empty("", ParseError::Empty)]
#[case::only_whitespace("    ", ParseError::Empty)]
#[case::fraction_without_whole_part(".1", ParseError::InvalidInput("Fraction without a whole number".to_owned()))]
#[case::fraction_without_whole_part_when_sec(".1sec", ParseError::InvalidInput("Fraction without a whole number".to_owned()))]
#[case::fraction_without_a_number("1.", ParseError::InvalidInput("Fraction without a fractional number".to_owned()))]
#[case::fraction_without_a_number_when_sec("1.sec", ParseError::InvalidInput("Fraction without a fractional number".to_owned()))]
#[case::two_fract_delimiter("2.\n0", ParseError::InvalidInput("Fraction without a fractional number".to_owned()))]
#[case::two_points("2..0", ParseError::InvalidInput("Fraction without a fractional number".to_owned()))]
#[case::exponent("1e2", ParseError::Syntax(1, "No exponent allowed".to_string()))]
#[case::infinity_short("inf", ParseError::InvalidInput("inf".to_string()))]
#[case::infinity_long("infinity", ParseError::InvalidInput("infinity".to_string()))]
#[case::ago_without_time_unit("1 ago", ParseError::InvalidInput("ago".to_string()))]
#[case::keyword_with_ago("today ago", ParseError::InvalidInput("ago".to_string()))]
#[case::fraction_when_fuzzy_unit(
    "1.1year",
    ParseError::InvalidInput("Fraction only allowed together with seconds as time unit".to_owned())
)]
#[case::fraction_when_not_second_time_unit(
    "1.1minute",
     ParseError::InvalidInput("Fraction only allowed together with seconds as time unit".to_owned())
)]
#[case::positive_years_overflow(
    &format!("{}year", "2".repeat(30)),
    ParseError::Overflow
)]
#[case::just_sign(
    "+",
    ParseError::Syntax(1, "Unexpected end of input. Sign without a number".to_owned())
)]
#[case::end_with_sign(
    "1sec +",
    ParseError::Syntax(6, "Unexpected end of input. Sign without a number".to_owned())
)]
#[case::end_with_sign_delimiter(
    "1sec +   ",
    ParseError::Syntax(6, "Unexpected end of input. Sign without a number".to_owned())
)]
fn test_parser_parse_invalid_input(#[case] input: &str, #[case] expected: ParseError) {
    assert_eq!(
        RelativeTimeParser::new().parse(input),
        Err(expected.clone())
    );
    assert_eq!(parse(input), Err(expected));
}

#[rstest]
#[case::too_short("s", ParseError::InvalidInput("s".to_string()))]
#[case::too_many("secondss", ParseError::InvalidInput("secondss".to_string()))]
fn test_parser_parse_with_invalid_time_units(#[case] input: &str, #[case] expected: ParseError) {
    assert_eq!(RelativeTimeParser::new().parse(input), Err(expected));
}

#[template]
#[rstest]
#[case::second(&["sec", "secs", "second", "seconds"], Duration::positive(1, 0))]
#[case::minute(&["min", "mins", "minute", "minutes"], Duration::positive(60, 0))]
#[case::hour(&["hour", "hours"], Duration::positive(60 * 60, 0))]
#[case::day(&["day", "days"], Duration::positive(60 * 60 * 24, 0))]
#[case::week(&["week", "weeks"], Duration::positive(60 * 60 * 24 * 7, 0))]
fn valid_time_units_template(#[case] time_units: &[&str], #[case] expected: Duration) {}

#[apply(valid_time_units_template)]
fn test_parser_parse_with_valid_time_units_blank(time_units: &[&str], expected: Duration) {
    for unit in time_units {
        assert_eq!(RelativeTimeParser::new().parse(unit), Ok(expected));
    }
}

#[apply(valid_time_units_template)]
fn test_parser_parse_with_valid_time_units_with_number(time_units: &[&str], expected: Duration) {
    for unit in time_units {
        assert_eq!(
            RelativeTimeParser::new().parse(&format!("1{unit}")),
            Ok(expected)
        );
    }
}

#[rstest]
#[case::minus_zero_second("-0second", Duration::ZERO)]
#[case::minus_one_second("-1second", Duration::negative(1, 0))]
#[case::minus_two_second("-2second", Duration::negative(2, 0))]
#[case::minus_second("-second", Duration::negative(1, 0))]
#[case::second_ago("second ago", Duration::negative(1, 0))]
#[case::plus_second_ago("+second ago", Duration::negative(1, 0))]
#[case::minus_second_ago("-second ago", Duration::positive(1, 0))]
#[case::minus_zero_minute("-0minute", Duration::ZERO)]
#[case::minus_one_minute("-1minute", Duration::negative(60, 0))]
#[case::minus_two_minute("-2minute", Duration::negative(120, 0))]
#[case::minus_minute("-minute", Duration::negative(60, 0))]
#[case::minute_ago("minute ago", Duration::negative(60, 0))]
#[case::plus_minute_ago("+minute ago", Duration::negative(60, 0))]
#[case::minus_minute_ago("-minute ago", Duration::positive(60, 0))]
fn test_parser_parse_with_just_time_unit_when_ago_or_negative(
    #[case] input: &str,
    #[case] expected: Duration,
) {
    assert_eq!(RelativeTimeParser::new().parse(input), Ok(expected));
}

#[cfg(feature = "time")]
#[rstest]
#[case::month(&["month", "months"], OffsetDateTime::from_unix_timestamp(0).unwrap().into(), Duration::positive(2678400, 0))] // Jan. 1970 has 31 days
#[case::year(&["year", "years"], OffsetDateTime::from_unix_timestamp(0).unwrap().into(), Duration::positive(31536000, 0))] // 1970 has 365 days
fn test_parser_parse_with_date_when_valid_fuzzy_time_units(
    #[case] time_units: &[&str],
    #[case] date: DateTime,
    #[case] expected: Duration,
) {
    for unit in time_units {
        assert_eq!(
            RelativeTimeParser::new().parse_with_date(unit, Some(date)),
            Ok(expected)
        );
        assert_eq!(parse_with_date(unit, Some(date)), Ok(expected));
    }
}

#[cfg(feature = "time")]
#[rstest]
#[case::max_date_plus_1ns(
    "+0.000000001sec",
    datetime!(+999999-12-31 23:59:59.999999999),
    Duration::positive(0, 1)
)]
#[case::minus_normal_year("-year", datetime!(1970-12-31 23:59:59.999999999), Duration::negative(31536000, 0))]
#[case::leap_year("year", datetime!(1972-01-01 00:00:00), Duration::positive(31622400, 0))] // 1972 is a leap year
#[case::leap_month("month", datetime!(1972-01-29 00:00:00), Duration::positive(2678400, 0))]
#[case::april_last_plus_month("month", datetime!(1970-04-30 00:00:00), Duration::positive(2592000, 0))]
#[case::min_date_plus_month("month", datetime!(-999999-01-01 00:00:00), Duration::positive(2678400, 0))]
#[case::minus_leap_year("-year", datetime!(1972-12-31 23:59:59.999999999), Duration::negative(31622400, 0))]
#[case::max_date_minus_year("-year", datetime!(+999999-12-31 23:59:59.999999999), Duration::negative(31536000, 0))]
#[case::last_january_minus_month("-month", datetime!(1970-01-31 00:00:00), Duration::negative(2678400, 0))]
#[case::first_january_minus_month("-month", datetime!(1970-01-01 00:00:00), Duration::negative(2678400, 0))]
#[case::first_january_minus_year("-year", datetime!(1970-01-01 00:00:00), Duration::negative(31536000, 0))]
#[case::first_january_minus_12month("-12month", datetime!(1970-01-01 00:00:00), Duration::negative(31536000, 0))]
#[case::first_january_minus_2year("-2year", datetime!(1970-01-01 00:00:00), Duration::negative(63158400, 0))]
#[case::first_january_minus_24month("-24month", datetime!(1970-01-01 00:00:00), Duration::negative(63158400, 0))]
#[case::duration_makes_date_valid("4days +month", datetime!(1970-01-28 00:00:00), Duration::positive(2764800, 0))]
#[case::duration_does_not_make_date_invalid(
    "1month 1day",
    datetime!(1970-01-28 00:00:00),
    Duration::positive(2764800, 0)
)]
#[case::no_leap_year_january_plus_month(
    "month",
    datetime!(1970-01-29 00:00:00),
    Duration::positive(2678400, 0)
)]
#[case::last_january_plus_month(
    "month",
    datetime!(1970-01-31 00:00:00),
    Duration::positive(2678400, 0)
)]
#[case::max_date_plus_leap_year(
    "+1year",
    datetime!(+999999-12-31 23:59:59.999999999),
    Duration::positive(31622400, 0)
)]
fn test_parser_parse_with_date_when_fuzzy(
    #[case] input: &str,
    #[case] date: PrimitiveDateTime,
    #[case] expected: Duration,
) {
    assert_eq!(
        RelativeTimeParser::new().parse_with_date(input, Some(date.into())),
        Ok(expected)
    );
    assert_eq!(parse_with_date(input, Some(date.into())), Ok(expected));
}

#[cfg(feature = "time")]
#[rstest]
#[case::leap_year_plus_secs("year +9sec", datetime!(1972-01-01 00:00:00), Duration::positive(31622409, 0))] // 1972 is a leap year
#[case::leap_year_plus_hours("year +9hour", datetime!(1972-01-01 00:00:00), Duration::positive(31654800, 0))] // 1972 is a leap year
#[case::leap_year_plus_hours_worth_days("year +100hour", datetime!(1972-01-01 00:00:00), Duration::positive(31982400, 0))] // 1972 is a leap year
#[case::leap_year_plus_hours_worth_days_plus_nanos("year +100hour +0.000000001", datetime!(1972-01-01 00:00:00), Duration::positive(31982400, 1))] // 1972 is a leap year
fn test_parser_parse_with_date_when_fuzzy_unit_and_normal_units(
    #[case] input: &str,
    #[case] date: PrimitiveDateTime,
    #[case] expected: Duration,
) {
    assert_eq!(
        RelativeTimeParser::new().parse_with_date(input, Some(date.into())),
        Ok(expected)
    );
    assert_eq!(parse_with_date(input, Some(date.into())), Ok(expected));
}

#[rstest]
#[case::yesterday("yesterday", Duration::negative(24 * 60 * 60, 0))]
#[case::tomorrow("tomorrow", Duration::positive(24 * 60 * 60, 0))]
#[case::today("today", Duration::ZERO)]
#[case::now("now", Duration::ZERO)]
fn test_parser_parse_with_valid_keywords(#[case] time_unit: &str, #[case] expected: Duration) {
    assert_eq!(RelativeTimeParser::new().parse(time_unit), Ok(expected));
}

#[rstest]
#[case::leading_spaces("    1sec")]
#[case::leading_all_posix_whitespace("\x09\x0A\x0B\x0C\x0D 1sec")]
#[case::trailing_whitespace("1sec   ")]
#[case::trailing_all_posix_whitespace("1sec \x09\x0A\x0B\x0C\x0D")]
#[case::leading_and_trailing("  1sec  ")]
fn test_parser_trims_whitespace(#[case] input: &str) {
    assert_eq!(
        RelativeTimeParser::new().parse(input),
        Ok(Duration::positive(1, 0))
    );
}

#[rstest]
#[case::number_one_too_high(&format!("{}", u64::MAX as u128 + 1), Duration::MAX)]
#[case::number_one_too_low(&format!("-{}", u64::MAX as u128 + 1), Duration::MIN)]
#[case::number_far_too_high(&format!("{}", u128::MAX), Duration::MAX)]
#[case::number_far_too_low(&format!("-{}", u128::MAX), Duration::MIN)]
#[case::time_unit_causes_positive_overflow(&format!("{}min", u64::MAX - 1), Duration::MAX)]
#[case::time_unit_causes_negative_overflow(&format!("-{}min", u64::MAX - 1), Duration::MIN)]
fn test_parser_when_overflow(#[case] input: &str, #[case] expected: Duration) {
    assert_eq!(RelativeTimeParser::new().parse(input), Ok(expected));
}

#[rstest]
#[case::when_positive_then_saturate(&format!("{}days", "2".repeat(20)), (0, 0, Duration::MAX))]
#[case::when_negative_then_saturate(&format!("-{}days", "2".repeat(20)), (0, 0, Duration::MIN))]
#[case::positive_years_overflow_then_saturate(&format!("{}year", "2".repeat(20)), (i64::MAX, 0, Duration::ZERO))]
#[case::positive_years_overflow_then_saturate(&format!("-{}year", "2".repeat(20)), (i64::MIN, 0, Duration::ZERO))]
#[case::negative_years_u64max_then_saturate(&format!("-{}year", u64::MAX), (i64::MIN, 0, Duration::ZERO))]
#[case::positive_years_u64max_then_saturate(&format!("{}year", u64::MAX), (i64::MAX, 0, Duration::ZERO))]
#[case::positive_months_overflow_then_saturate(&format!("{}month", "2".repeat(20)), (0, i64::MAX, Duration::ZERO))]
#[case::negative_months_overflow_then_saturate(&format!("-{}month", "2".repeat(20)), (0, i64::MIN, Duration::ZERO))]
#[case::years_and_month_overflow_then_saturate(&format!("{0}year {0}month", "2".repeat(20)), (i64::MAX, i64::MAX, Duration::ZERO))]
fn test_parser_parse_fuzzy(#[case] input: &str, #[case] expected: (i64, i64, Duration)) {
    assert_eq!(RelativeTimeParser::new().parse_fuzzy(input), Ok(expected));
    assert_eq!(parse_fuzzy(input), Ok(expected));
}

#[rstest]
fn test_parser_numerals_with_not_fuzzy_time_units(
    #[values(
        ("last", -1),
        ("this", 0),
        ("next", 1),
        ("first", 1),
        ("third", 3),
        ("fourth", 4),
        ("fifth", 5),
        ("sixth", 6),
        ("seventh", 7),
        ("eighth", 8),
        ("ninth", 9),
        ("tenth", 10),
        ("eleventh", 11),
        ("twelfth", 12)
    )]
    input: (&str, i64),
    #[values(("sec", Second), ("min", Minute))] time_unit: (&str, TimeUnit),
) {
    let (source, coefficient) = input;
    let (id, unit) = time_unit;
    let Multiplier(c, _) = unit.multiplier();
    let seconds = c * coefficient;
    assert_eq!(
        RelativeTimeParser::new().parse(&format!("{source} {id}")),
        Ok(Duration::from_std(
            seconds.is_negative(),
            StdDuration::new(seconds.unsigned_abs(), 0)
        ))
    );
}

#[rstest]
#[case::last_ago("last minute ago", Duration::positive(60, 0))]
#[case::this_ago("this minute ago", Duration::ZERO)]
#[case::next_ago("next minute ago", Duration::negative(60, 0))]
#[case::third_ago("third minute ago", Duration::negative(3 * 60, 0))]
fn test_parser_numerals_not_fuzzy_time_units_when_ago(
    #[case] input: &str,
    #[case] expected: Duration,
) {
    assert_eq!(RelativeTimeParser::new().parse(input), Ok(expected));
}

#[rstest]
#[case::last_year("last year", Duration::negative(365 * 24 * 60 * 60, 0))]
#[case::plus_last_year("+last year", Duration::negative(365 * 24 * 60 * 60, 0))]
#[case::minus_last_year("-last year", Duration::positive(365 * 24 * 60 * 60, 0))]
#[case::last_year_ago("last year ago", Duration::positive(365 * 24 * 60 * 60, 0))]
#[case::this_year("this year", Duration::ZERO)]
#[case::minus_this_year("-this year", Duration::ZERO)]
#[case::this_year_ago("this year ago", Duration::ZERO)]
#[case::next_year("next year", Duration::positive(365 * 24 * 60 * 60, 0))]
#[case::plus_next_year("+next year", Duration::positive(365 * 24 * 60 * 60, 0))]
#[case::minus_next_year("-next year", Duration::negative(365 * 24 * 60 * 60, 0))]
#[case::next_year_ago("next year ago", Duration::negative(365 * 24 * 60 * 60, 0))]
#[case::plus_next_year_ago("+next year ago", Duration::negative(365 * 24 * 60 * 60, 0))]
#[case::minus_next_year_ago("-next year ago", Duration::positive(365 * 24 * 60 * 60, 0))]
#[case::third_year("third year", Duration::positive(365 * 24 * 60 * 60 * 2 + 366 * 24 * 60 * 60, 0))]
#[case::third_year_ago("third year ago", Duration::negative(365 * 24 * 60 * 60 * 2 + 366 * 24 * 60 * 60, 0))]
fn test_parser_numerals_with_fuzzy_time_unit(#[case] input: &str, #[case] expected: Duration) {
    assert_eq!(
        RelativeTimeParser::new().parse_with_date(
            input,
            Some(DateTime::from_gregorian_date_time(1970, 8, 1, 0, 0, 0, 0))
        ),
        Ok(expected)
    );
}

#[rstest]
#[case::plus_year("+year", Duration::positive(365 * 24 * 60 * 60, 0))]
#[case::minus_year("-year", Duration::negative(365 * 24 * 60 * 60, 0))]
#[case::minus_year_ago("-year ago", Duration::positive(365 * 24 * 60 * 60, 0))]
#[case::minus_one_year("-1year", Duration::negative(365 * 24 * 60 * 60, 0))]
#[case::minus_two_year("-2year", Duration::negative(365 * 2 * 24 * 60 * 60, 0))]
#[case::minus_one_year_ago("-1year ago", Duration::positive(365 * 24 * 60 * 60, 0))]
#[case::minus_two_year_ago("-2year ago", Duration::positive((365 + 366) * 24 * 60 * 60, 0))]
#[case::year_ago("year ago", Duration::negative(365 * 24 * 60 * 60, 0))]
fn test_parser_with_fuzzy_time_unit_when_ago_or_sign(
    #[case] input: &str,
    #[case] expected: Duration,
) {
    assert_eq!(
        RelativeTimeParser::new().parse_with_date(
            input,
            Some(DateTime::from_gregorian_date_time(1970, 8, 1, 0, 0, 0, 0))
        ),
        Ok(expected)
    );
}
