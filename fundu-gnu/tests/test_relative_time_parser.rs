// spell-checker: ignore secondss
// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu_gnu::{Duration, ParseError, RelativeTimeParser};
use rstest::rstest;

const YEAR: u64 = 60 * 60 * 24 * 365 + 60 * 60 * 24 / 4; // 365 days + day/4
const MONTH: u64 = YEAR / 12;

#[rstest]
#[case::zero("0", Duration::ZERO)]
#[case::minus_zero("-0", Duration::ZERO)]
#[case::just_number("1", Duration::positive(1, 0))]
#[case::number_with_plus_sign("+1", Duration::positive(1, 0))]
#[case::time_unit_without_number("sec", Duration::positive(1, 0))]
#[case::time_unit_with_plus_sign("+sec", Duration::positive(1, 0))]
#[case::number_with_whitespace_between_time_unit("1 sec", Duration::positive(1, 0))]
#[case::number_with_all_whitespace_between_time_unit(
    "1\x09\x0A\x0B\x0C\x0D sec",
    Duration::positive(1, 0)
)]
#[case::negative("-1", Duration::negative(1, 0))]
#[case::ago("1 sec ago", Duration::negative(1, 0))]
#[case::ago_with_all_whitespace("1 sec\x09\x0A\x0B\x0C\x0D ago", Duration::negative(1, 0))]
#[case::negative_with_ago("-1 sec ago", Duration::positive(1, 0))]
#[case::multiple("1 sec 1 sec", Duration::positive(2, 0))]
#[case::multiple_with_all_whitespace("1 sec\x09\x0A\x0B\x0C\x0D 1 sec", Duration::positive(2, 0))]
#[case::multiple_with_ago("1 sec ago 1 sec", Duration::ZERO)]
#[case::fraction_when_no_time_unit("1.1", Duration::positive(1, 100_000_000))]
#[case::fraction_when_second_time_unit("1.1sec", Duration::positive(1, 100_000_000))]
fn test_parser_parse_valid_input(#[case] input: &str, #[case] expected: Duration) {
    assert_eq!(RelativeTimeParser::new().parse(input), Ok(expected));
    assert_eq!(fundu_gnu::parse(input), Ok(expected));
}

#[rstest]
#[case::empty("", ParseError::Empty)]
#[case::only_whitespace("    ", ParseError::Empty)]
#[case::exponent("1e2", ParseError::Syntax(1, "No exponent allowed".to_string()))]
#[case::infinity_short("inf", ParseError::TimeUnit(0, "Invalid time unit: 'inf'".to_string()))]
#[case::infinity_long("infinity", ParseError::TimeUnit(0, "Invalid time unit: 'infinity'".to_string()))]
#[case::ago_without_time_unit("1 ago", ParseError::TimeUnit(2, "Invalid time unit: 'ago'".to_string()))]
#[case::keyword_with_ago("today ago", ParseError::TimeUnit(6, "Invalid time unit: 'ago'".to_string()))]
#[case::fraction_when_not_second_time_unit("1.1year", ParseError::InvalidInput("Fraction only allowed together with seconds as time unit".to_owned()))]
fn test_parser_parse_invalid_input(#[case] input: &str, #[case] expected: ParseError) {
    assert_eq!(
        RelativeTimeParser::new().parse(input),
        Err(expected.clone())
    );
    assert_eq!(fundu_gnu::parse(input), Err(expected));
}

#[rstest]
#[case::too_short("s", ParseError::TimeUnit(0, "Invalid time unit: 's'".to_string()))]
#[case::too_many("secondss", ParseError::TimeUnit(0, "Invalid time unit: 'secondss'".to_string()))]
fn test_parser_parse_with_invalid_time_units(#[case] input: &str, #[case] expected: ParseError) {
    assert_eq!(RelativeTimeParser::new().parse(input), Err(expected));
}

#[rstest]
#[case::second(&["sec", "secs", "second", "seconds"], Duration::positive(1, 0))]
#[case::minute(&["min", "mins", "minute", "minutes"], Duration::positive(60, 0))]
#[case::hour(&["hour", "hours"], Duration::positive(60 * 60, 0))]
#[case::day(&["day", "days"], Duration::positive(60 * 60 * 24, 0))]
#[case::week(&["week", "weeks"], Duration::positive(60 * 60 * 24 * 7, 0))]
#[case::month(&["month", "months"], Duration::positive(MONTH, 0))]
#[case::year(&["year", "years"], Duration::positive(YEAR, 0))]
fn test_parser_parse_with_valid_time_units(
    #[case] time_units: &[&str],
    #[case] expected: Duration,
) {
    for unit in time_units {
        assert_eq!(RelativeTimeParser::new().parse(unit), Ok(expected));
    }
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
