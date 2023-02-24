#![no_main]

use std::{num::IntErrorKind, time::Duration};

use fundu::{DurationParser, ParseError};
use libfuzzer_sys::fuzz_target;

fn check_exponent_overflow(input: &str, error: ParseError) {
    match input.find(|c: char| c.eq_ignore_ascii_case(&'e')) {
        Some(index) => match input.get(index + 1..) {
            Some(exponent) => {
                match exponent.parse::<i16>() {
                    Ok(e) if (-1022..=1023).contains(&e) => panic!(
                        "Exponent overflow error: Exponent was in valid range: input: {input}, error: {error:?}"
                    ),
                    Ok(_) => {
                        // The overflow error is correctly returned by the parser
                    }
                    Err(error) => match error.kind() {
                        IntErrorKind::PosOverflow | IntErrorKind::NegOverflow => {
                            // The overflow error is correctly returned by the parser
                        }
                        kind => panic!(
                            "Exponent overflow error: Should not be an Overflow error: {input}, error: {error:?}, kind: {kind:?}"
                        ),
                    }
                }
            }
            None => panic!("Exponent overflow error: No number: input: {input}, error: {error:?}"),
        },
        None => {
            panic!("Exponent overflow error: No exponent: input: {input}, error: {error:?}");
        }
    }
}

fuzz_target!(|data: &[u8]| {
    let parser = DurationParser::without_time_units();
    if let Ok(string) = std::str::from_utf8(data) {
        if let Ok(parsed) = string.parse::<f64>() {
            if !parsed.is_nan() && parsed.is_sign_negative() && parsed != 0f64 {
                match &parsed.abs().partial_cmp(&0.000000000000000001f64) {
                    // Every negative number x with abs(x) < 1e-18 resolves to a zero duration but
                    // in case of an exponent overflow the error is returned.
                    Some(std::cmp::Ordering::Less) => {
                        if let Err(error) = parser.parse(string) {
                            match error {
                                ParseError::NegativeExponentOverflow
                                | ParseError::PositiveExponentOverflow => {
                                    check_exponent_overflow(string, error)
                                }
                                _ => panic!("Expected no error: input: {string}, error: {error:?}"),
                            }
                        }
                    }
                    Some(std::cmp::Ordering::Equal) => {
                        // This is an edge case for which a statement about the correctness of fundu
                        // is impossible due to the inaccuracy of the f64 comparison. For example
                        // -.9999999e-18 == -1e-18. fundu doesn't round and resolves -.9999999e-18
                        // to a zero duration, which is the correct behavior. So, this case doesn't
                        // suit for fuzzy testing here and has to be tested separately in a unit or
                        // integration test.
                    }
                    // Negative numbers x with abs(x) >= 1e-18 should be detected as negative
                    // number and fundu returns an error
                    Some(std::cmp::Ordering::Greater) | None => {
                        if let Ok(duration) = parser.parse(string) {
                            panic!(
                                "Expected an error: input: {string}, f64: {parsed}, duration: {duration:?}"
                            );
                        }
                    }
                }
            // fundu doesn't understand NaN
            } else if parsed.is_nan() {
                if let Ok(duration) = parser.parse(string) {
                    panic!(
                        "Expected an error: input: {string}, f64: {parsed}, duration: {duration:?}"
                    );
                }
            // Everything else should be parsable by fundu besides some special handling of the exponent
            // and the overflow errors
            } else {
                match parser.parse(string) {
                    Ok(duration) => {
                        let rust_duration = match Duration::try_from_secs_f64(parsed) {
                            Ok(d) => d,
                            Err(_) => Duration::MAX,
                        };
                        // This epsilon is backed by a lot of random runs and manual comparisons
                        let epsilon_duration = Duration::from_secs(1024);
                        let delta = duration
                            .max(rust_duration)
                            .saturating_sub(duration.min(rust_duration));
                        if delta > epsilon_duration {
                            panic!("The duration delta between rust and fundu was too high: input: {string}, fundu: {duration:?}, rust: {rust_duration:?}, epsilon: {epsilon_duration:?}, delta: {delta:?}")
                        }
                    }
                    Err(error) => match error {
                        fundu::ParseError::NegativeExponentOverflow
                        | fundu::ParseError::PositiveExponentOverflow => {
                            check_exponent_overflow(string, error)
                        }
                        _ => {
                            panic!("Expected no error: input: {string}, error: {error:?}");
                        }
                    },
                }
            }
        // What can't be parsed to a f64 can't be parsed by fundu
        } else if let Ok(parsed) = parser.parse(string) {
            panic!("Expected an error: input: {string}, duration: {parsed:?}");
        }
    }
});
