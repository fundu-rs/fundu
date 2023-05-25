// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

#![no_main]

use arbitrary::Arbitrary;
use fundu::DurationParser;
use libfuzzer_sys::fuzz_target;
use regex::Regex;

const DELIMITER: fn(u8) -> bool =
    |byte| matches!(byte, b' ' | b'\t' | b'\n' | b'\x0c' | b'\r' | b'\x0b');

#[derive(Arbitrary, Debug)]
struct FuzzingConfig<'a> {
    input: &'a str,
    allow_negative: bool,
    allow_delimiter: bool,
    disable_infinity: bool,
    disable_exponent: bool,
    disable_fraction: bool,
    number_is_optional: bool,
}

fn generate_regex(config: FuzzingConfig) -> Regex {
    let sign = if config.allow_negative {
        r"[+-]?"
    } else {
        r"[+]?"
    };
    let delimiter_number_time_unit = if config.allow_delimiter {
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
    let time_unit = r"(w|d|h|m|s|ms|Ms|ns)";
    let regex =
        format!("{infinity}({number}(({delimiter_number_time_unit}{time_unit})|{time_unit}?))");
    regex::Regex::new(&format!("^(?P<sign>{sign})({regex})$")).unwrap()
}

fuzz_target!(|config: FuzzingConfig| {
    let mut parser = DurationParser::new();
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
        .number_is_optional(config.number_is_optional);

    let input = config.input;
    let re = generate_regex(config);
    let captures = re.captures(input);
    let expect_success = captures.is_some();
    match parser.parse(input) {
        Ok(_) if expect_success => {}
        Ok(duration) => {
            if duration.is_zero() && input.starts_with('-') {
            } else {
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
                // false positive may happen when number_is_optional == true
                fundu::ParseError::Syntax(_, _) if input == "+" || input == "-" => {}
                _ => panic!("Expected a duration but got an error: {}", error),
            }
        }
        Err(_) => {}
    };
});
