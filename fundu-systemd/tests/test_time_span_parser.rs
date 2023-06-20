// spell-checker: ignore Dinfinity infinit infinitys

// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::{Duration, ParseError, TimeUnit};
use fundu_systemd::{
    parse, parse_nanos, TimeSpanParser, SYSTEMD_MAX_NSEC_DURATION, SYSTEMD_MAX_USEC_DURATION,
};
use rstest::rstest;

const YEAR: u64 = 60 * 60 * 24 * 365 + 60 * 60 * 24 / 4; // 365 days + day/4
const MONTH: u64 = YEAR / 12;
const MAX_USEC_DURATION_SECS: u64 = u64::MAX / 1_000_000;
const MAX_USEC_DURATION_NANO: u32 = (u64::MAX % 1_000_000) as u32 * 1000;

#[rstest]
#[case::empty("", ParseError::Empty)]
#[case::negative("-1", ParseError::NegativeNumber)]
#[case::only_point(".", ParseError::Syntax(0, "Either the whole number part or the fraction must be present".to_string()))]
#[case::two_points_leading("..1", ParseError::Syntax(0, "Either the whole number part or the fraction must be present".to_string()))]
#[case::two_points_trailing("1..", ParseError::TimeUnit(2, "Invalid time unit: '.'".to_string()))]
#[case::exponent("234e10", ParseError::Syntax(3, "No exponent allowed".to_string()))]
#[case::invalid_time_unit("3.invalid", ParseError::TimeUnit(2, "Invalid time unit: 'invalid'".to_string()))]
fn test_parse_parse_when_invalid(#[case] input: &str, #[case] expected: ParseError) {
    assert_eq!(TimeSpanParser::new().parse(input), Err(expected.clone()));
    assert_eq!(parse(input, None, None), Err(expected.clone()));
    assert_eq!(
        TimeSpanParser::new().parse_nanos(input),
        Err(expected.clone())
    );
    assert_eq!(parse_nanos(input, None, None), Err(expected));
}

#[rstest]
#[case::short_inf("inf", ParseError::TimeUnit(0, "Invalid time unit: 'inf'".to_string()))]
#[case::capitalized("Infinity", ParseError::TimeUnit(0, "Invalid time unit: 'Infinity'".to_string()))]
#[case::one_letter_less("infinit", ParseError::TimeUnit(0, "Invalid time unit: 'infinit'".to_string()))]
#[case::one_letter_too_much("infinitys", ParseError::TimeUnit(0, "Invalid time unit: 'infinitys'".to_string()))]
fn test_parser_parse_infinity_when_invalid_then_error(
    #[case] input: &str,
    #[case] expected: ParseError,
) {
    assert_eq!(TimeSpanParser::new().parse(input), Err(expected.clone()));
    assert_eq!(parse(input, None, None), Err(expected.clone()));
    assert_eq!(
        TimeSpanParser::new().parse_nanos(input),
        Err(expected.clone())
    );
    assert_eq!(parse_nanos(input, None, None), Err(expected));
}

#[rstest]
#[case::simple("infinity")]
#[case::leading_spaces("    infinity")]
#[case::leading_all_posix_whitespace("\x09\x0A\x0B\x0C\x0D infinity")]
#[case::trailing_whitespace("infinity   ")]
#[case::trailing_spaces("infinity \x09\x0A\x0B\x0C\x0D")]
fn test_parser_parse_infinity(#[case] input: &str) {
    assert_eq!(
        TimeSpanParser::new().parse(input),
        Ok(SYSTEMD_MAX_USEC_DURATION)
    );
    assert_eq!(parse(input, None, None), Ok(SYSTEMD_MAX_USEC_DURATION));
    assert_eq!(
        TimeSpanParser::new().parse_nanos(input),
        Ok(SYSTEMD_MAX_NSEC_DURATION)
    );
    assert_eq!(
        parse_nanos(input, None, None),
        Ok(SYSTEMD_MAX_NSEC_DURATION)
    );
}

#[rstest]
#[case::micro(&["us", "\u{03BC}s", "\u{00B5}s", "usec"], Duration::positive(0, 1_000))]
#[case::micro_sign(&["µs",], Duration::positive(0, 1_000))]
#[case::greek_mu(&["μs",], Duration::positive(0, 1_000))]
#[case::milli(&["ms",  "msec"], Duration::positive(0, 1_000_000))]
#[case::second(&["s", "sec", "second", "seconds"], Duration::positive(1, 0))]
#[case::minute(&["m", "min", "minute", "minutes"], Duration::positive(60, 0))]
#[case::hour(&["h", "hr", "hour", "hours"], Duration::positive(60 * 60, 0))]
#[case::day(&["d", "day", "days"], Duration::positive(60 * 60 * 24, 0))]
#[case::week(&["w", "week", "weeks"], Duration::positive(60 * 60 * 24 * 7, 0))]
#[case::month(&["M", "month", "months"], Duration::positive(MONTH, 0))]
#[case::year(&["y", "year", "years"], Duration::positive(YEAR, 0))]
fn test_parser_parse_with_valid_time_units(
    #[case] time_units: &[&str],
    #[case] expected: Duration,
) {
    for unit in time_units {
        assert_eq!(TimeSpanParser::new().parse(unit), Ok(expected));
    }
}

#[rstest]
#[case::nano("nsec", ParseError::TimeUnit(0, "Invalid time unit: 'nsec'".to_string()))]
#[case::nano("ns", ParseError::TimeUnit(0, "Invalid time unit: 'ns'".to_string()))]
fn test_parser_parse_when_invalid_time_units(#[case] input: &str, #[case] expected: ParseError) {
    assert_eq!(TimeSpanParser::new().parse(input), Err(expected.clone()));
    assert_eq!(parse(input, None, None), Err(expected));
}

#[rstest]
#[case::max_duration_plus_one_sec(&format!("{}.{}", MAX_USEC_DURATION_SECS + 1, MAX_USEC_DURATION_NANO))]
#[case::max_duration_plus_one_nano(&format!("{}.{}", MAX_USEC_DURATION_SECS, MAX_USEC_DURATION_NANO + 1))]
#[case::exact_max_duration(&format!("{}.{}", MAX_USEC_DURATION_SECS, MAX_USEC_DURATION_NANO))]
#[case::large_just_number(&"1".repeat(1022))]
#[case::barely_with_multiple_durations("1year 10000years 100000years 14975376516109.55s 1616usec")]
fn test_parser_parse_when_saturating(#[case] input: &str) {
    assert_eq!(
        TimeSpanParser::new().parse(input),
        Ok(SYSTEMD_MAX_USEC_DURATION)
    );
    assert_eq!(parse(input, None, None), Ok(SYSTEMD_MAX_USEC_DURATION));
}

#[rstest]
#[case::max_duration_with_usec_time_unit(&format!("{}us", u64::MAX), Duration::positive(MAX_USEC_DURATION_SECS, MAX_USEC_DURATION_NANO))]
#[case::max_duration_with_usec_time_unit_minus_one(&format!("{}us", u64::MAX - 1), Duration::positive(MAX_USEC_DURATION_SECS, MAX_USEC_DURATION_NANO - 1_000))]
#[case::max_duration_minus_one_sec(&format!("{}.{}", MAX_USEC_DURATION_SECS - 1, MAX_USEC_DURATION_NANO), Duration::positive(MAX_USEC_DURATION_SECS - 1, MAX_USEC_DURATION_NANO))]
#[case::max_duration_minus_one_nano(&format!("{}.{}", MAX_USEC_DURATION_SECS, MAX_USEC_DURATION_NANO -1), Duration::positive(MAX_USEC_DURATION_SECS, MAX_USEC_DURATION_NANO - 1))]
#[case::max_duration_minus_one_micro(&format!("{}.{}", MAX_USEC_DURATION_SECS, MAX_USEC_DURATION_NANO -1000), Duration::positive(MAX_USEC_DURATION_SECS, MAX_USEC_DURATION_NANO - 1000))]
fn test_parser_parse_when_barely_not_saturating(#[case] input: &str, #[case] expected: Duration) {
    assert_eq!(TimeSpanParser::new().parse(input), Ok(expected));
    assert_eq!(parse(input, None, None), Ok(expected));
}

#[rstest]
#[case::nanos(&["ns",  "nsec"], Duration::positive(0, 1))]
#[case::micro(&["us", "\u{03BC}s", "μs", "\u{00B5}s", "µs", "usec"], Duration::positive(0, 1_000))]
#[case::milli(&["ms",  "msec"], Duration::positive(0, 1_000_000))]
#[case::second(&["s", "sec", "second", "seconds"], Duration::positive(1, 0))]
#[case::minute(&["m", "min", "minute", "minutes"], Duration::positive(60, 0))]
#[case::hour(&["h", "hr", "hour", "hours"], Duration::positive(60 * 60, 0))]
#[case::day(&["d", "day", "days"], Duration::positive(60 * 60 * 24, 0))]
#[case::week(&["w", "week", "weeks"], Duration::positive(60 * 60 * 24 * 7, 0))]
#[case::month(&["M", "month", "months"], Duration::positive(MONTH, 0))]
#[case::year(&["y", "year", "years"], Duration::positive(YEAR, 0))]
fn test_parser_parse_with_nanos_with_valid_time_units(
    #[case] time_units: &[&str],
    #[case] expected: Duration,
) {
    for unit in time_units {
        assert_eq!(TimeSpanParser::new().parse_nanos(unit), Ok(expected));
        assert_eq!(parse_nanos(unit, None, None), Ok(expected));
    }
}

#[rstest]
#[case::none(
    "123.123",
    Some(TimeUnit::Second),
    Duration::positive(123, 123_000_000)
)]
#[case::second(
    "123.123",
    Some(TimeUnit::Second),
    Duration::positive(123, 123_000_000)
)]
#[case::smaller_than_second("123.123", Some(TimeUnit::MicroSecond), Duration::positive(0, 123_123))]
#[case::larger_than_second(
    "123.123",
    Some(TimeUnit::Year),
    Duration::positive(3885466384, 800_000_000)
)]
#[case::nano_second("123.123", Some(TimeUnit::NanoSecond), Duration::positive(0, 123))]
fn test_parse_and_parse_nanos_with_time_units(
    #[case] input: &str,
    #[case] time_unit: Option<TimeUnit>,
    #[case] expected: Duration,
) {
    assert_eq!(parse(input, time_unit, None), Ok(expected));
    assert_eq!(parse_nanos(input, time_unit, None), Ok(expected));
}

#[rstest]
#[case::none("123.123", None, Duration::positive(123, 123_000_000))]
#[case::none_when_saturating("123456789y", None, SYSTEMD_MAX_USEC_DURATION)]
#[case::duration_zero("123.123", Some(Duration::ZERO), Duration::ZERO)]
#[case::duration_max("123.123", Some(Duration::MAX), Duration::positive(123, 123_000_000))]
#[case::duration_max_when_saturating(&format!("{}", u128::MAX), Some(Duration::MAX), Duration::MAX)]
#[case::duration_middle(
    "123456",
    Some(Duration::positive(123456, 789)),
    Duration::positive(123456, 0)
)]
#[case::duration_middle_when_saturating(
    "123457",
    Some(Duration::positive(123456, 789)),
    Duration::positive(123456, 789)
)]
fn test_parse_with_max(
    #[case] input: &str,
    #[case] max: Option<Duration>,
    #[case] expected: Duration,
) {
    assert_eq!(parse(input, None, max), Ok(expected));
}

#[rstest]
#[case::negative_zero(Duration::negative(0, 0))]
#[case::negative(Duration::negative(1, 0))]
#[should_panic]
fn test_parse_with_invalid_max_then_panic(#[case] max: Duration) {
    _ = parse("123", None, Some(max));
}

#[rstest]
#[case::negative_zero(Duration::negative(0, 0))]
#[case::negative(Duration::negative(1, 0))]
#[should_panic]
fn test_parse_nanos_with_invalid_max_then_panic(#[case] max: Duration) {
    _ = parse_nanos("123", None, Some(max));
}
