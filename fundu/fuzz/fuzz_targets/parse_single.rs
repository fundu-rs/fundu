// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

#![no_main]

use arbitrary::Arbitrary;
use fundu::{CustomDurationParser, Multiplier, TimeKeyword, TimeUnit, DEFAULT_TIME_UNITS};
use libfuzzer_sys::fuzz_target;
use regex::Regex;

const DELIMITER: fn(u8) -> bool =
    |byte| matches!(byte, b' ' | b'\t' | b'\n' | b'\x0c' | b'\r' | b'\x0b');
const DELIMITER_CHARS: &[char] = &[' ', '\t', '\n', '\x0c', '\r', '\x0b'];

#[derive(Arbitrary, Debug)]
struct FuzzingConfig<'a> {
    input: &'a str,
    allow_negative: bool,
    allow_delimiter: bool,
    disable_infinity: bool,
    disable_exponent: bool,
    disable_fraction: bool,
    number_is_optional: bool,
    allow_ago: bool,
    keyword: KeywordsChoice,
    allow_sign_delimiter: bool,
}

#[derive(Arbitrary, Debug, PartialEq, Eq)]
enum KeywordsChoice {
    None,
    Positive,
    PositiveNegative,
    PositiveNegativeZero,
}

impl KeywordsChoice {
    fn generate_regex(&self) -> String {
        match self {
            KeywordsChoice::None => "",
            KeywordsChoice::Positive => r"(tomorrow)|",
            KeywordsChoice::PositiveNegative => r"(yesterday|tomorrow)|",
            KeywordsChoice::PositiveNegativeZero => r"(yesterday|tomorrow|today)|",
        }
        .to_string()
    }

    fn get_time_keywords(&self) -> Vec<TimeKeyword> {
        match self {
            KeywordsChoice::None => vec![],
            KeywordsChoice::Positive => {
                vec![TimeKeyword::new(
                    TimeUnit::Day,
                    &["tomorrow"],
                    Some(Multiplier(1, 0)),
                )]
            }
            KeywordsChoice::PositiveNegative => {
                vec![
                    TimeKeyword::new(TimeUnit::Day, &["yesterday"], Some(Multiplier(-1, 0))),
                    TimeKeyword::new(TimeUnit::Day, &["tomorrow"], Some(Multiplier(1, 0))),
                ]
            }
            KeywordsChoice::PositiveNegativeZero => {
                vec![
                    TimeKeyword::new(TimeUnit::Day, &["yesterday"], Some(Multiplier(-1, 0))),
                    TimeKeyword::new(TimeUnit::Day, &["tomorrow"], Some(Multiplier(1, 0))),
                    TimeKeyword::new(TimeUnit::Second, &["today"], Some(Multiplier(0, 0))),
                ]
            }
        }
    }
}

fn generate_regex(config: &FuzzingConfig) -> Regex {
    let sign = if config.allow_negative || config.allow_ago {
        if config.allow_sign_delimiter {
            r"([+-][ \t\n\x0c\r\x0b]*)?"
        } else {
            r"[+-]?"
        }
    } else if config.allow_sign_delimiter {
        r"([+][ \t\n\x0c\r\x0b]*)?"
    } else {
        r"[+]?"
    };
    let delimiter = if config.allow_delimiter {
        r"[ \t\n\x0c\r\x0b]+"
    } else {
        ""
    };
    let infinity = if config.disable_infinity {
        ""
    } else {
        r"([iI][nN][fF])|([iI][nN][fF][iI][nN][iI][tT][yY])|"
    };
    let base = if config.disable_fraction {
        r"(?P<base>[[:digit:]]+)"
    } else {
        r"(?P<base>([[:digit:]]+)|([[:digit:]]+\.[[:digit:]]*)|([[:digit:]]*\.[[:digit:]]+))"
    };
    let exponent = if config.disable_exponent {
        ""
    } else {
        r"([eE](?P<exponent>[+-]?[[:digit:]]+))?"
    };
    let number = if config.number_is_optional {
        format!("({base}{exponent})?")
    } else {
        format!("{base}{exponent}")
    };
    let ago = if config.allow_ago {
        r"([ \t\n\x0c\r\x0b]+[aA][gG][oO])?"
    } else {
        ""
    };
    let keyword = config.keyword.generate_regex();
    let time_unit = r"(w|d|h|m|s|ms|Ms|ns)";
    let regex =
        format!("{infinity}{keyword}({number}(({delimiter}{time_unit}{ago})|({time_unit}{ago}))?)");
    regex::Regex::new(&format!("^(?P<sign>{sign})({regex})$")).unwrap()
}

fuzz_target!(|config: FuzzingConfig| {
    let mut parser = CustomDurationParser::with_time_units(&DEFAULT_TIME_UNITS);
    parser
        .allow_negative(config.allow_negative)
        .allow_delimiter(if config.allow_delimiter {
            Some(DELIMITER)
        } else {
            None
        })
        .disable_infinity(config.disable_infinity)
        .disable_fraction(config.disable_fraction)
        .disable_exponent(config.disable_exponent)
        .number_is_optional(config.number_is_optional)
        .allow_ago(if config.allow_ago {
            Some(DELIMITER)
        } else {
            None
        })
        .allow_sign_delimiter(if config.allow_sign_delimiter {
            Some(DELIMITER)
        } else {
            None
        });
    if config.keyword != KeywordsChoice::None {
        parser.keywords(&config.keyword.get_time_keywords());
    }

    let input = config.input;
    let re = generate_regex(&config);
    let captures = re.captures(input);
    let expect_success = captures.is_some();
    match parser.parse(input) {
        Ok(_) if expect_success => {}
        Ok(duration) => {
            if (duration.is_zero() && input.starts_with('-'))
                || ((config.keyword == KeywordsChoice::PositiveNegative
                    || config.keyword == KeywordsChoice::PositiveNegativeZero)
                    && input == "-yesterday")
            {
            } else {
                dbg!(re);
                panic!("Expected an error but got a duration: {:?}", duration)
            }
        }
        Err(error) if expect_success => {
            let captures = captures.unwrap();
            match error {
                fundu::ParseError::NegativeExponentOverflow => {
                    if let Ok(exp) = captures.name("exponent").unwrap().as_str().parse::<i16>() {
                        panic!("Expected negative exponent overflow but got: {}", exp)
                    }
                }
                fundu::ParseError::PositiveExponentOverflow => {
                    if let Ok(exp) = captures.name("exponent").unwrap().as_str().parse::<i16>() {
                        panic!("Expected positive exponent overflow but got: {}", exp)
                    }
                }
                fundu::ParseError::Empty => {
                    // false positive may happen when number_is_optional == true
                    if !input.is_empty() {
                        panic!("Expected an empty input if ParseError::Empty is returned")
                    }
                }
                // false positive may happen when parsing negative numbers is not enabled but
                // keyword evaluates to a negative duration
                fundu::ParseError::NegativeNumber
                    if !config.allow_negative
                        && !config.allow_ago
                        && (config.keyword == KeywordsChoice::PositiveNegative
                            || config.keyword == KeywordsChoice::PositiveNegativeZero)
                        && (input == "yesterday" || input == "+yesterday") => {}
                // false positive may happen when number_is_optional == true
                fundu::ParseError::Syntax(_, _)
                    if input == "+" || input == "-" || input.starts_with(DELIMITER_CHARS) => {}
                // false positive may happen when allow_sign_delimiter is set
                fundu::ParseError::Syntax(_, _)
                    if config.allow_sign_delimiter && input.ends_with(DELIMITER_CHARS) => {}
                fundu::ParseError::InvalidInput(_) | fundu::ParseError::TimeUnit(_, _)
                    if !config.allow_sign_delimiter
                        && input.starts_with(['+', '-'])
                        && input
                            .get(1..)
                            .map_or(false, |rem| rem.starts_with(DELIMITER_CHARS)) => {}
                fundu::ParseError::InvalidInput(_) | fundu::ParseError::TimeUnit(_, _)
                    if input.starts_with(DELIMITER_CHARS) => {}
                _ => {
                    dbg!(re);
                    panic!("Expected a duration but got an error: {}", error)
                }
            }
        }
        Err(_) => {}
    };
});
