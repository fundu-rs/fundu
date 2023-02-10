#![no_main]

use fundu::DurationParser;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let mut parser = DurationParser::without_time_units();
    if let Ok(string) = std::str::from_utf8(data) {
        if let Ok(parsed) = string.parse::<f64>() {
            if !parsed.is_nan() && parsed.is_sign_negative() && parsed != 0f64 {
                match &parsed.abs().partial_cmp(&0.000000000000000001f64) {
                    Some(std::cmp::Ordering::Less) => {
                        if let Err(error) = parser.parse(string) {
                            panic!("Expected no error: input: {string}, error: {error:?}");
                        }
                    }
                    Some(std::cmp::Ordering::Equal) | Some(std::cmp::Ordering::Greater) | None => {
                        if let Ok(duration) = parser.parse(string) {
                            panic!(
                                "Expected an error: input: {string}, f64: {parsed}, duration: {duration:?}"
                            );
                        }
                    }
                }
            } else if parsed.is_nan() {
                if let Ok(duration) = parser.parse(string) {
                    panic!(
                        "Expected an error: input: {string}, f64: {parsed}, duration: {duration:?}"
                    );
                }
            } else if let Err(error) = parser.parse(&format!("{parsed}")) {
                panic!("Expected no error: input: {string}, error: {error:?}");
            }
        } else if let Ok(parsed) = parser.parse(string) {
            panic!("Expected an error: input: {string}, duration: {parsed:?}");
        }
    }
});
