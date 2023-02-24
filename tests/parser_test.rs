// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::{parse_duration, DurationParser, ParseError, TimeUnit, TimeUnit::*};
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
fn test_parse_duration_with_illegal_argument_then_error(#[case] source: &str) {
    let result = parse_duration(source);
    // cov:excl-start
    assert!(
        result.is_err(),
        "Expected an error but result was: {result:?}"
    ); // cov:excl-stop
}

#[rstest]
#[case::simple_zero("0", Duration::ZERO)]
#[case::many_zeroes(&"0".repeat(2000), Duration::ZERO)]
#[case::many_leading_zeroes(&format!("{}1", "0".repeat(2000)), Duration::new(1, 0))]
#[case::zero_point_zero("0.0", Duration::ZERO)]
#[case::point_zero(".0", Duration::ZERO)]
#[case::zero_point("0.", Duration::ZERO)]
#[case::simple_number("1", Duration::new(1, 0))]
#[case::one_with_fraction_number("1.1", Duration::new(1, 100_000_000))]
#[case::leading_zero_max_nanos("0.999999999", Duration::new(0, 999_999_999))]
#[case::leading_number_max_nanos("1.999999999", Duration::new(1, 999_999_999))]
#[case::simple_number("1234.123456789", Duration::new(1234, 123_456_789))]
#[case::max_seconds(&u64::MAX.to_string(), Duration::new(u64::MAX, 0))]
#[case::leading_zeros("000000100", Duration::new(100, 0))]
#[case::leading_zeros_with_fraction("00000010.0", Duration::new(10, 0))]
#[case::trailing_zeros("10.010000000", Duration::new(10, 10_000_000))]
#[case::negative_number_negative_exponent_below_attos("-9.99999999999E-19", Duration::ZERO)]
fn test_parse_duration_when_simple_arguments_are_valid(
    #[case] source: &str,
    #[case] expected: Duration,
) {
    let duration = parse_duration(source).unwrap();
    assert_eq!(duration, expected);
}

#[rstest]
#[case::zero("1.1e0", Duration::new(1, 100_000_000))]
#[case::point_and_then_exponent("1.e0", Duration::new(1, 0))]
#[case::negative_zero("1.1e-0", Duration::new(1, 100_000_000))]
#[case::simple("1.09e1", Duration::new(10, 900_000_000))]
#[case::simple_big_e("1.09E1", Duration::new(10, 900_000_000))]
#[case::lower_than_nanos_min("0.0000000001e1", Duration::new(0, 1))]
#[case::higher_than_seconds_max(&format!("{}9.999999999e-1", u64::MAX), Duration::MAX)]
#[case::plus_sign("0.1000000001e+1", Duration::new(1, 1))]
#[case::minus_sign_whole_to_fract("1.00000001e-1", Duration::new(0, 100_000_001))]
#[case::minus_sign_zero_to_fract("10.00000001e-1", Duration::new(1, 1))]
#[case::no_overflow_error_low("1.0e-1022", Duration::ZERO)]
#[case::no_overflow_error_high("1.0e1023", Duration::MAX)]
#[case::maximum_amount_of_seconds_digits_no_overflow(&format!("{}.0e-1022", "1".repeat(1042)), Duration::new(11_111_111_111_111_111_111, 111_111_111))]
#[case::more_than_maximum_amount_of_seconds_digits_then_maximum_duration(&format!("{}.0e-1022", "1".repeat(1043)), Duration::MAX)]
#[case::amount_of_nano_seconds_digits_then_capped(&format!("0.{}9e+1023", "0".repeat(1032)), Duration::ZERO)]
#[case::maximum_amount_of_nano_seconds_digits_then_not_capped(&format!("0.{}9e+1023", "0".repeat(1031)), Duration::new(0, 9))]
fn test_parse_duration_when_arguments_contain_exponent(
    #[case] source: &str,
    #[case] expected: Duration,
) {
    let duration = parse_duration(source).unwrap();
    assert_eq!(duration, expected);
}

#[rstest]
#[case::no_number("1e")]
#[case::invalid_number("1e+F")]
#[case::exponent_overflow_error_high("1e1024")]
#[case::exponent_overflow_error_low("1e-1023")]
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
#[case::max_attos_no_u64_overflow(&format!("0.{}y", "9".repeat(100)), Duration::new(31557599, 999_999_999))]
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
    "1e-1023",
    ParseError::NegativeExponentOverflow,
    "Negative exponent overflow: Minimum is -1022"
)]
#[case::positive_exponent_overflow_error(
    DurationParser::new(),
    "1e+1024",
    ParseError::PositiveExponentOverflow,
    "Positive exponent overflow: Maximum is +1023"
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
