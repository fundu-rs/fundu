// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::{
    parse_duration, CustomDurationParser, DurationParser, ParseError, TimeUnit, TimeUnit::*,
    SYSTEMD_TIME_UNITS,
};
use rstest::rstest;
use std::time::Duration;

const YEAR: u64 = 60 * 60 * 24 * 365 + 60 * 60 * 24 / 4; // 365 days + day/4
const MONTH: u64 = YEAR / 12;

#[rstest]
#[case::empty_string("")]
#[case::leading_whitespace("  1")]
#[case::trailing_whitespace("1   ")]
#[case::trailing_invalid_character("1.1e1msNOPE")]
#[case::only_whitespace("  \t\n")]
#[case::only_point(".")]
#[case::only_sign("+")]
#[case::only_exponent("e-10")]
#[case::sign_with_exponent("-e1")]
#[case::sign_with_point_and_exponent("-.e1")]
#[case::negative_seconds("-1")]
#[case::negative_seconds_with_fraction("-1.0")]
#[case::negative_nano_seconds("-0.000000001")]
#[case::exponent_with_only_plus("2E+")]
#[case::negative_number_high_exponent("-3E75")]
#[case::negative_number_barely_not_zero("-1.e-18")]
#[case::negative_number_1("-.00000000000019999999e-4")]
#[case::negative_number_2("-.00000003e-2")]
#[case::negative_large_input_with_high_exponent("-088888888888888888888888818288833333333333333333333333333333333333333333333388888888888888888880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001616564957e-1027")]
fn test_parse_duration_with_illegal_argument_then_error(#[case] source: &str) {
    let result = parse_duration(source);
    // cov:excl-start
    assert!(
        result.is_err(),
        "Expected an error but result was: {result:?}"
    ); // cov:excl-stop
}

#[rstest]
#[case::simple_number("1", Duration::new(1, 0))]
#[case::trailing_zeros("10.010000000", Duration::new(10, 10_000_000))]
#[case::simple_zero("0", Duration::ZERO)]
#[case::many_zeroes(&"0".repeat(2000), Duration::ZERO)]
#[case::many_leading_zeroes(&format!("{}1", "0".repeat(2000)), Duration::new(1, 0))]
#[case::zero_point_zero("0.0", Duration::ZERO)]
#[case::point_zero(".0", Duration::ZERO)]
#[case::zero_point("0.", Duration::ZERO)]
#[case::one_with_fraction_number("1.1", Duration::new(1, 100_000_000))]
#[case::leading_zero_max_nanos("0.999999999", Duration::new(0, 999_999_999))]
#[case::leading_number_max_nanos("1.999999999", Duration::new(1, 999_999_999))]
#[case::simple_number("1234.123456789", Duration::new(1234, 123_456_789))]
#[case::max_seconds(&u64::MAX.to_string(), Duration::new(u64::MAX, 0))]
#[case::leading_zeros("000000100", Duration::new(100, 0))]
#[case::leading_zeros_with_fraction("00000010.0", Duration::new(10, 0))]
#[case::negative_number_negative_exponent_below_attos("-9.99999999999E-19", Duration::ZERO)]
#[case::negative_large_input_with_high_exponent_is_zero("-.000000000000000000000000000000000000011888888888888888888888888888880000000000003333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333888888888888888888888888888888888800003333333333333333333333333333333333333333333333333333333333333333333333333338888888888888888833333333333333333333333333333333333333333333333338888888888888833333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333338888888888888888888888888888888888888888888888885888888000000000000333333333333333333333333333338883333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333888888888888888888888888888888888888888888888888888888800000000000033333333333333333000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000011414703819657838596", Duration::ZERO)]
#[case::f64_max(&format!("{}", f64::MAX), Duration::MAX)]
fn test_parse_duration_when_simple_arguments_are_valid(
    #[case] source: &str,
    #[case] expected: Duration,
) {
    let duration = parse_duration(source).unwrap();
    assert_eq!(duration, expected);
}

#[rstest]
#[case::minus_sign_whole_to_fract("1.00000001e-1", Duration::new(0, 100_000_001))]
#[case::zero("1.1e0", Duration::new(1, 100_000_000))]
#[case::point_and_then_exponent("1.e0", Duration::new(1, 0))]
#[case::negative_zero("1.1e-0", Duration::new(1, 100_000_000))]
#[case::simple("1.09e1", Duration::new(10, 900_000_000))]
#[case::simple_big_e("1.09E1", Duration::new(10, 900_000_000))]
#[case::two_e4("2e4", Duration::new(20000, 0))]
#[case::lower_than_nanos_min("0.0000000001e1", Duration::new(0, 1))]
#[case::higher_than_seconds_max(&format!("{}9.999999999e-1", u64::MAX), Duration::MAX)]
#[case::plus_sign("0.1000000001e+1", Duration::new(1, 1))]
#[case::minus_sign_zero_to_fract("10.00000001e-1", Duration::new(1, 1))]
#[case::no_overflow_error_low("1.0e-32768", Duration::ZERO)]
#[case::no_overflow_error_high("1.0e+32767", Duration::MAX)]
#[case::maximum_exponent(&format!("0.{}9e+{}", "0".repeat(i16::MAX as usize), i16::MAX), Duration::new(0, 900_000_000))]
#[case::maximum_exponent_barely_not_zero(&format!(".{}1e{}", "0".repeat((i16::MAX as usize) + 8), i16::MAX), Duration::new(0, 1))]
#[case::maximum_exponent_barely_not_zero_with_time_unit(&format!(".{}1e{}y", "0".repeat((i16::MAX as usize) + 15), i16::MAX), Duration::new(0, 3))]
#[case::maximum_exponent_with_maximum_time_unit(&format!("0.{}9e+{}y", "0".repeat(i16::MAX as usize), i16::MAX), Duration::new(28401840, 0))]
#[case::minimum_exponent(&format!("1{}.0e{}", "0".repeat(i16::MIN.unsigned_abs() as usize), i16::MIN), Duration::new(1, 0))]
#[case::minimum_exponent_barely_not_max_duration(&format!("1{}.0e{}", "0".repeat((i16::MIN.unsigned_abs() as usize) + 19), i16::MIN), Duration::new(10_000_000_000_000_000_000, 0))]
#[case::minimum_exponent_barely_not_max_duration_with_time_unit(&format!("1{}.0e{}ns", "0".repeat((i16::MIN.unsigned_abs() as usize) + 28), i16::MIN), Duration::new(10_000_000_000_000_000_000, 0))]
#[case::minimum_exponent_with_minimum_time_unit(&format!("1{}.0e{}ns", "0".repeat((i16::MAX as usize) + 1), i16::MIN), Duration::new(0, 1))]
fn test_parse_duration_when_arguments_contain_exponent(
    #[case] source: &str,
    #[case] expected: Duration,
) {
    let duration = DurationParser::with_all_time_units().parse(source).unwrap();
    assert_eq!(duration, expected);
}

#[rstest]
#[case::no_number("1e")]
#[case::invalid_number("1e+F")]
#[case::exponent_overflow_error_high("1e32768")]
#[case::exponent_overflow_error_low("1e-32769")]
#[case::exponent_parse_i16_overflow_error(&format!("1e{}", i16::MIN as i32 - 1))]
fn test_parse_duration_when_arguments_with_illegal_exponent_then_error(#[case] source: &str) {
    assert!(parse_duration(source).is_err());
}

#[rstest]
#[case::no_rounding("1.99999999999999999", Duration::new(1, 999_999_999))]
#[case::high_value_no_swallow_fract(&format!("{}.1", u64::MAX),Duration::new(u64::MAX, 100_000_000) )]
fn test_parse_duration_when_precision_of_float_would_be_insufficient_then_still_parse_exact(
    #[case] source: &str,
    #[case] expected: Duration,
) {
    let duration = parse_duration(source).unwrap();
    assert_eq!(duration, expected);
}

#[rstest]
#[case::lower_than_min_nanos("1.0000000001", Duration::new(1, 0))]
#[case::max_digits_of_nanos("1.99999999999", Duration::new(1, 999_999_999))]
#[case::higher_than_max_seconds(&format!("{}", u64::MAX as u128 + 1), Duration::MAX)]
#[case::higher_than_max_seconds_with_fraction(&format!("{}.0", u64::MAX as u128 + 1), Duration::MAX)]
fn test_parse_duration_when_arguments_are_capped_then_max_duration_or_min_nanos(
    #[case] source: &str,
    #[case] expected: Duration,
) {
    let duration = parse_duration(source).unwrap();
    assert_eq!(duration, expected);
}

#[rstest]
#[case::plus_zero("+0", Duration::ZERO)]
#[case::plus_zero_with_fraction("+0.0", Duration::ZERO)]
#[case::minus_zero("-0", Duration::ZERO)]
#[case::minus_zero_with_fraction("-0.0", Duration::ZERO)]
#[case::plus_one_with_fraction("+1.0", Duration::new(1, 0))]
fn test_parse_duration_when_arguments_have_a_sign(
    #[case] source: &str,
    #[case] expected: Duration,
) {
    let duration = parse_duration(source).unwrap();
    assert_eq!(duration, expected);
}

#[rstest]
#[case::infinity_short("inf")]
#[case::infinity_short_case_insensitive("iNf")]
#[case::infinity_long("infinity")]
#[case::infinity_long_case_insensitive("InfiNitY")]
fn test_parse_duration_when_arguments_are_infinity_values(#[case] source: &str) {
    let duration = parse_duration(source).unwrap();
    assert_eq!(duration, Duration::MAX);
}

#[rstest]
#[case::negative_infinity_short("-inf")]
#[case::negative_infinity_long("-infinity")]
#[case::infinity_long_trailing_invalid("infinityINVALID")]
#[case::incomplete_infinity("infin")]
#[case::infinity_with_number("inf1.0")]
fn test_parse_duration_when_arguments_are_illegal_infinity_values_then_error(#[case] source: &str) {
    assert!(parse_duration(source).is_err());
}

#[rstest]
#[case::max_attos_no_u64_overflow(&format!("0.{}y", "9".repeat(100)), Duration::new(31557599, 999_999_999))]
#[case::seconds("1s", Duration::new(1, 0))]
#[case::milli_seconds("1ms", Duration::new(0, 1_000_000))]
#[case::milli_seconds("1000ms", Duration::new(1, 0))]
#[case::micro_seconds("1Ms", Duration::new(0, 1_000))]
#[case::micro_seconds("1e-3Ms", Duration::new(0, 1))]
#[case::nano_seconds_time_unit("1ns", Duration::new(0, 1))]
#[case::minutes_fraction("0.1m", Duration::new(6, 0))]
#[case::minutes_negative_exponent("100.0e-3m", Duration::new(6, 0))]
#[case::minutes_underflow("0.0000000001m", Duration::new(0, 6))]
#[case::hours_underflow("0.000000000001h", Duration::new(0, 3))]
#[case::years_underflow("0.0000000000000001y", Duration::new(0, 3))]
#[case::minutes_overflow(&format!("{}m", u64::MAX), Duration::MAX)]
fn test_parse_duration_when_time_units_are_given(#[case] source: &str, #[case] expected: Duration) {
    let duration = DurationParser::with_all_time_units().parse(source).unwrap();
    assert_eq!(duration, expected);
}

#[rstest]
#[case::seconds("1s", vec![TimeUnit::Second])]
#[case::hour("1h", vec![TimeUnit::Hour])]
fn test_parser_when_time_units(#[case] source: &str, #[case] time_units: Vec<TimeUnit>) {
    DurationParser::with_time_units(&time_units)
        .parse(source)
        .unwrap();
}

#[rstest]
#[case::minute_short("1s", vec![TimeUnit::Minute])]
fn test_parser_when_time_units_are_not_present_then_error(
    #[case] source: &str,
    #[case] time_units: Vec<TimeUnit>,
) {
    assert!(DurationParser::without_time_units()
        .time_units(time_units.as_slice())
        .parse(source)
        .is_err());
}

#[rstest]
#[case::empty("", ParseError::Empty)]
#[case::only_space(" ", ParseError::Syntax(0, "Invalid character: ' '".to_string()))]
#[case::space_before_number(" 123", ParseError::Syntax(0, "Invalid character: ' '".to_string()))]
#[case::space_at_end_of_input("123 ns ", ParseError::TimeUnit(4, "Invalid time unit: 'ns '".to_string()))]
#[case::other_whitespace("123\tns", ParseError::TimeUnit(3, "Invalid time unit: '\tns'".to_string()))]
fn test_parser_when_allow_spaces_then_error(#[case] input: &str, #[case] expected: ParseError) {
    let mut parser = DurationParser::with_all_time_units();
    parser.allow_spaces();
    assert_eq!(parser.parse(input).unwrap_err(), expected);
}

#[rstest]
#[case::without_spaces("123ns", Duration::new(0, 123))]
#[case::single_space("123 ns", Duration::new(0, 123))]
#[case::multiple_spaces("123      ns", Duration::new(0, 123))]
fn test_parser_when_allow_spaces(#[case] input: &str, #[case] expected: Duration) {
    let mut parser = DurationParser::with_all_time_units();
    parser.allow_spaces();
    assert_eq!(parser.parse(input).unwrap(), expected);
}

#[rstest]
#[case::minute_short("1s", TimeUnit::Minute)]
fn test_parser_when_custom_time_unit_then_error(#[case] source: &str, #[case] time_unit: TimeUnit) {
    assert!(DurationParser::without_time_units()
        .time_unit(time_unit)
        .parse(source)
        .is_err());
}

#[rstest]
#[case::time_unit_error_when_no_time_units(
    DurationParser::without_time_units(),
    "1y",
    ParseError::TimeUnit(1, "No time units allowed but found: 'y'".to_string()),
    "Time unit error: No time units allowed but found: 'y' at column 1"
)]
#[case::time_unit_error_when_all_time_units(
    DurationParser::with_all_time_units(),
    "1years",
    ParseError::TimeUnit(1, "Invalid time unit: 'years'".to_string()),
    "Time unit error: Invalid time unit: 'years' at column 1"
)]
#[case::negative_exponent_overflow_error(
    DurationParser::new(),
    "1e-32769",
    ParseError::NegativeExponentOverflow,
    "Negative exponent overflow: Minimum is -32768"
)]
#[case::positive_exponent_overflow_error(
    DurationParser::new(),
    "1e+32768",
    ParseError::PositiveExponentOverflow,
    "Positive exponent overflow: Maximum is +32767"
)]
#[case::negative_number_error(
    DurationParser::new(),
    "-1",
    ParseError::NegativeNumber,
    "Number was negative"
)]
#[case::negative_number_when_infinity_error(
    DurationParser::new(),
    "-inf",
    ParseError::NegativeNumber,
    "Number was negative"
)]
fn test_parse_error_messages(
    #[case] parser: DurationParser,
    #[case] input: &str,
    #[case] expected_error: ParseError,
    #[case] expected_string: &str,
) {
    assert_eq!(parser.parse(input), Err(expected_error));
    assert_eq!(
        parser.parse(input).unwrap_err().to_string(),
        expected_string
    );
}

#[rstest]
#[case::nano_second(NanoSecond, Duration::new(0, 1))]
#[case::micro_second(MicroSecond, Duration::new(0, 1_000))]
#[case::milli_second(MilliSecond, Duration::new(0, 1_000_000))]
#[case::second(Second, Duration::new(1, 0))]
#[case::minute(Minute, Duration::new(60, 0))]
#[case::hour(Hour, Duration::new(60 * 60, 0))]
#[case::day(Day, Duration::new(60 * 60 * 24, 0))]
#[case::week(Week, Duration::new(60 * 60 * 24 * 7, 0))]
#[case::month(Month, Duration::new(MONTH, 0))]
#[case::year(Year, Duration::new(YEAR, 0))]
fn test_parser_setting_default_time_unit(#[case] time_unit: TimeUnit, #[case] expected: Duration) {
    assert_eq!(
        DurationParser::without_time_units()
            .default_unit(time_unit)
            .parse("1")
            .unwrap(),
        expected
    );
}

#[rstest]
#[case::nano_second(&["ns", "nsec"], Duration::new(0, 1))]
#[case::micro_second(&["us", "µs", "usec"], Duration::new(0, 1000))]
#[case::milli_second(&["ms", "msec"], Duration::new(0, 1_000_000))]
#[case::second(&["s", "sec", "second", "seconds"], Duration::new(1, 0))]
#[case::minute(&["m", "min", "minute", "minutes"], Duration::new(60, 0))]
#[case::hour(&["h", "hr", "hour", "hours"], Duration::new(60 * 60, 0))]
#[case::day(&["d", "day", "days"], Duration::new(60 * 60 * 24, 0))]
#[case::week(&["w", "week", "weeks"], Duration::new(60 * 60 * 24 * 7, 0))]
#[case::month(&["M", "month", "months"], Duration::new(MONTH, 0))]
#[case::year(&["y", "year", "years"], Duration::new(YEAR, 0))]
fn test_custom_duration_parser_parse_when_systemd_time_units(
    #[case] inputs: &[&str],
    #[case] expected: Duration,
) {
    let parser = CustomDurationParser::with_time_units(&SYSTEMD_TIME_UNITS);
    for input in inputs {
        assert_eq!(parser.parse(&format!("1{input}")), Ok(expected));
    }
}
