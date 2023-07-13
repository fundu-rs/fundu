// spell-checker: ignore nextsecond

// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu_core::config::{ConfigBuilder, Delimiter, Numeral};
use fundu_core::error::ParseError;
use fundu_core::parse::Parser;
use fundu_core::time::{Duration, Multiplier, TimeUnit, TimeUnitsLike};
use rstest::{fixture, rstest};

struct TwoTimeUnits {}
impl TimeUnitsLike for TwoTimeUnits {
    fn is_empty(&self) -> bool {
        false
    }

    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        match identifier {
            "second" => Some((TimeUnit::Second, Multiplier::default())),
            "minute" => Some((TimeUnit::Minute, Multiplier::default())),
            _ => None,
        }
    }
}

struct EmptyTimeUnits {}
impl TimeUnitsLike for EmptyTimeUnits {
    fn is_empty(&self) -> bool {
        true
    }

    fn get(&self, _: &str) -> Option<(TimeUnit, Multiplier)> {
        None
    }
}

struct TomorrowKeyword {}
impl TimeUnitsLike for TomorrowKeyword {
    // cov:excl-start
    fn is_empty(&self) -> bool {
        false
    }
    // cov:excl-stop

    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        match identifier {
            "tomorrow" => Some((TimeUnit::Day, Multiplier::default())),
            _ => None,
        }
    }
}

#[fixture]
fn two_time_units() -> Box<dyn TimeUnitsLike> {
    Box::new(TwoTimeUnits {})
}

#[fixture]
fn empty_time_units() -> Box<dyn TimeUnitsLike> {
    Box::new(EmptyTimeUnits {})
}

#[fixture]
fn tomorrow_keyword() -> Box<dyn TimeUnitsLike> {
    Box::new(TomorrowKeyword {})
}

#[fixture]
fn two_numerals() -> Vec<Numeral<'static>> {
    vec![
        Numeral::new(&["next"], Multiplier::default()),
        Numeral::new(&["three"], Multiplier(3, 0)),
    ]
}

#[fixture]
fn space_delimiter() -> Delimiter {
    |byte| matches!(byte, b' ')
}

#[rstest]
#[case::numeral_next_second("next second", Duration::positive(1, 0))]
#[case::numeral_three_second("three second", Duration::positive(3, 0))]
#[case::numeral_next_minute("next minute", Duration::positive(60, 0))]
#[case::numeral_three_minute("three minute", Duration::positive(180, 0))]
#[case::numeral_with_multiple_delimiter("next        second", Duration::positive(1, 0))]
#[case::just_keyword("tomorrow", Duration::positive(86400, 0))]
fn test_parse_with_numerals(
    #[case] input: &str,
    #[case] expected: Duration,
    two_time_units: Box<dyn TimeUnitsLike>,
    tomorrow_keyword: Box<dyn TimeUnitsLike>,
    two_numerals: Vec<Numeral<'static>>,
    space_delimiter: Delimiter,
) {
    let config = ConfigBuilder::new()
        .allow_numerals(&two_numerals, space_delimiter)
        .build();
    let parser = Parser::with_config(config);
    assert_eq!(
        parser.parse(
            input,
            two_time_units.as_ref(),
            Some(tomorrow_keyword.as_ref())
        ),
        Ok(expected)
    );
}

#[rstest]
#[case::numeral_with_positive_sign("+next second", Duration::positive(1, 0))]
#[case::numeral_with_delimited_positive_sign("+ next second", Duration::positive(1, 0))]
#[case::numeral_with_negative_sign("-next second", Duration::negative(1, 0))]
#[case::numeral_with_delimited_negative_sign("- next second", Duration::negative(1, 0))]
fn test_parse_with_numerals_when_sign_is_present(
    #[case] input: &str,
    #[case] expected: Duration,
    two_time_units: Box<dyn TimeUnitsLike>,
    tomorrow_keyword: Box<dyn TimeUnitsLike>,
    two_numerals: Vec<Numeral<'static>>,
    space_delimiter: Delimiter,
) {
    let config = ConfigBuilder::new()
        .allow_numerals(&two_numerals, space_delimiter)
        .allow_sign_delimiter(space_delimiter)
        .allow_negative()
        .build();
    let parser = Parser::with_config(config);
    assert_eq!(
        parser.parse(
            input,
            two_time_units.as_ref(),
            Some(tomorrow_keyword.as_ref())
        ),
        Ok(expected)
    );
}

#[rstest]
#[case::just_time_unit("second", Duration::positive(1, 0))]
#[case::just_keyword("tomorrow", Duration::positive(86400, 0))]
fn test_parse_with_numerals_when_number_is_optional(
    #[case] input: &str,
    #[case] expected: Duration,
    two_time_units: Box<dyn TimeUnitsLike>,
    tomorrow_keyword: Box<dyn TimeUnitsLike>,
    two_numerals: Vec<Numeral<'static>>,
    space_delimiter: Delimiter,
) {
    let config = ConfigBuilder::new()
        .allow_numerals(&two_numerals, space_delimiter)
        .number_is_optional()
        .build();
    let parser = Parser::with_config(config);
    assert_eq!(
        parser.parse(
            input,
            two_time_units.as_ref(),
            Some(tomorrow_keyword.as_ref())
        ),
        Ok(expected)
    );
}

#[rstest]
#[case::numeral_without_delimiter("nextsecond", ParseError::InvalidInput("nextsecond".to_owned()))]
#[case::numeral_with_wrong_delimiter("next\nsecond", ParseError::InvalidInput("next\nsecond".to_owned()))]
#[case::incomplete_numeral("nex second", ParseError::InvalidInput("nex second".to_owned()))]
#[case::just_numeral("next", ParseError::InvalidInput("next".to_owned()))]
#[case::numeral_end_with_delimiter("next    ", ParseError::Syntax(4, "Input may not end with a delimiter".to_owned()))]
#[case::numeral_with_keyword("next tomorrow", ParseError::TimeUnit(5, "Invalid time unit: 'tomorrow'".to_owned()))]
#[case::numeral_with_wrong_time_unit("next hour", ParseError::TimeUnit(5, "Invalid time unit: 'hour'".to_owned()))]
fn test_parse_with_numerals_when_invalid(
    #[case] input: &str,
    #[case] expected: ParseError,
    two_time_units: Box<dyn TimeUnitsLike>,
    tomorrow_keyword: Box<dyn TimeUnitsLike>,
    two_numerals: Vec<Numeral<'static>>,
    space_delimiter: Delimiter,
) {
    let config = ConfigBuilder::new()
        .allow_numerals(&two_numerals, space_delimiter)
        .build();
    let parser = Parser::with_config(config);
    assert_eq!(
        parser.parse(
            input,
            two_time_units.as_ref(),
            Some(tomorrow_keyword.as_ref())
        ),
        Err(expected)
    );
}

#[rstest]
#[case::numeral_without_time_unit("next 1", ParseError::TimeUnit(5, "Found numeral 'next' without a time unit".to_owned()))]
#[case::numeral_without_time_unit_plus("next +", ParseError::TimeUnit(5, "Found numeral 'next' without a time unit".to_owned()))]
#[case::two_next("next next", ParseError::TimeUnit(5, "Found numeral 'next' without a time unit".to_owned()))]
fn test_parse_with_numerals_when_invalid_parse_multiple(
    #[case] input: &str,
    #[case] expected: ParseError,
    two_time_units: Box<dyn TimeUnitsLike>,
    tomorrow_keyword: Box<dyn TimeUnitsLike>,
    two_numerals: Vec<Numeral<'static>>,
    space_delimiter: Delimiter,
) {
    let config = ConfigBuilder::new()
        .allow_numerals(&two_numerals, space_delimiter)
        .parse_multiple(space_delimiter, None)
        .build();
    let parser = Parser::with_config(config);
    assert_eq!(
        parser.parse(
            input,
            two_time_units.as_ref(),
            Some(tomorrow_keyword.as_ref())
        ),
        Err(expected)
    );
}

#[rstest]
#[case::numeral_with_impossible_time_unit(
    "next second",
    ParseError::TimeUnit(5, "Found numeral 'next' without time units being defined".to_owned())
)]
#[case::numeral_without_time_unit(
    "next 1",
    ParseError::TimeUnit(5, "Found numeral 'next' without time units being defined".to_owned())
)]
#[case::impossible_keyword("tomorrow", ParseError::InvalidInput("tomorrow".to_owned()))]
fn test_parse_with_numerals_when_empty_time_units_no_keywords_and_parse_multiple(
    #[case] input: &str,
    #[case] expected: ParseError,
    empty_time_units: Box<dyn TimeUnitsLike>,
    two_numerals: Vec<Numeral<'static>>,
    space_delimiter: Delimiter,
) {
    let config = ConfigBuilder::new()
        .allow_numerals(&two_numerals, space_delimiter)
        .parse_multiple(space_delimiter, None)
        .build();
    let parser = Parser::with_config(config);
    assert_eq!(
        parser.parse(input, empty_time_units.as_ref(), None),
        Err(expected)
    );
}
