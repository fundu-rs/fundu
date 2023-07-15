// spell-checker: ignore fract libfuzzer nanos
#![no_main]

use std::ops::Neg;
use std::time::Duration as StdDuration;

use fundu_gnu::{Duration, ParseError, RelativeTimeParser};
use lazy_static::lazy_static;
use libfuzzer_sys::fuzz_target;
use regex::Regex;

const DELIMITER_CHARS: &[char] = &[' ', '\t', '\n', '\x0c', '\r', '\x0b'];

const RE_DELIMITER: &str = r"[ \t\n\x0c\r\x0b]";
const RE_NUMERAL: &str =
    r"(last|this|next|first|third|fourth|fifth|sixth|seventh|eighth|ninth|tenth|eleventh|twelfth)";
const RE_TIME_UNIT: &str = r"(seconds|second|secs|sec|minutes|minute|mins|min|hours|hour|days|day|weeks|week|fortnights|fortnight|months|month|years|year)";
const RE_TIME_UNIT_NOT_SEC: &str = r"(minutes|minute|mins|min|hours|hour|days|day|weeks|week|fortnights|fortnight|months|month|years|year)";
const RE_KEYWORD: &str = r"(yesterday|today|now|tomorrow)";
const RE_AGO: &str = r"[aA][gG][oO]";

/// The main regex used to verify that the input string is grammatically correct
fn generate_regex() -> Regex {
    let duration = format!(
        r"([+-]{RE_DELIMITER}*)?({RE_KEYWORD}|({RE_NUMERAL}{RE_DELIMITER}+{RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|({RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|([[:digit:]]+{RE_DELIMITER}*{RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|([[:digit:]]+\.[[:digit:]]+{RE_DELIMITER}*{RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|([[:digit:]]+\.[[:digit:]]+)|([[:digit:]]+))"
    );
    let duration_sign = format!(
        r"([+-]{RE_DELIMITER}*)({RE_KEYWORD}|({RE_NUMERAL}{RE_DELIMITER}+{RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|({RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|([[:digit:]]+{RE_DELIMITER}*{RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|([[:digit:]]+\.[[:digit:]]+{RE_DELIMITER}*{RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|([[:digit:]]+\.[[:digit:]]+)|([[:digit:]]+))"
    );
    let duration_digit = format!(
        r"(([[:digit:]]+{RE_DELIMITER}*{RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|([[:digit:]]+\.[[:digit:]]+{RE_DELIMITER}*{RE_TIME_UNIT}({RE_DELIMITER}+{RE_AGO})?)|([[:digit:]]+\.[[:digit:]]+)|([[:digit:]]+))"
    );
    regex::Regex::new(&format!(
        r"^(({duration})(({duration_digit})|({duration_sign})|({RE_DELIMITER}+({duration})))*?)$"
    ))
    .unwrap()
}

/// A control regex which matches correct input the main regex wasn't able to figure out
fn generate_control_regex() -> Regex {
    regex::Regex::new(&format!(r"(([[:digit:]]+|[[:digit:]]+\.[[:digit]]+)(({RE_NUMERAL}{RE_DELIMITER}+{RE_TIME_UNIT})|{RE_KEYWORD})({RE_DELIMITER}+{RE_AGO})?)")).unwrap()
}

/// A control regex which matches incorrect fractions the main regex wasn't able to figure out
fn generate_fraction_control_regex() -> Regex {
    regex::Regex::new(&format!(
        r"(([[:digit:]]+\.[[:digit:]]+)(\.|({RE_DELIMITER}*{RE_TIME_UNIT_NOT_SEC})))"
    ))
    .unwrap()
}

/// This regex is used to extract the durations from the input string. It is based on the premise
/// that the string, used to match this regex, is already verified to be grammatically correct.
/// Therefore, it can be a lot simpler than the regex validating the grammar.
fn generate_extraction_regex() -> Regex {
    let regex = format!(
        r"(?P<duration>((?P<sign>[+-]){RE_DELIMITER}*)?((?P<keyword>{RE_KEYWORD})|(?P<numeral>(?P<numeral_value>{RE_NUMERAL}){RE_DELIMITER}*(?P<numeral_time_unit>{RE_TIME_UNIT}))|((?P<digits>((?P<whole>[[:digit:]]+)\.(?P<fract>[[:digit:]]+))|(?P<number>[[:digit:]]+))?{RE_DELIMITER}*(?P<time_unit>{RE_TIME_UNIT})?))?{RE_DELIMITER}*(?P<ago>{RE_AGO})?)"
    );
    regex::Regex::new(&regex).unwrap()
}

lazy_static! {
    pub static ref REGEX: Regex = generate_regex();
    pub static ref CONTROL_REGEX: Regex = generate_control_regex();
    pub static ref FRACTION_CONTROL_REGEX: Regex = generate_fraction_control_regex();
    pub static ref EXTRACTION_REGEX: Regex = generate_extraction_regex();
}

/// Extract the durations from the input string using the EXTRACTION_REGEX. The result should be
/// same as returned by [`RelativeTimeParser::parse_fuzzy`].
fn extract(input: &str) -> (i64, i64, Duration) {
    let mut duration = Duration::ZERO;
    let mut years = 0i64;
    let mut months = 0i64;

    fn parse_numeral(numeral: &str) -> i64 {
        match numeral {
            "last" => -1,
            "this" => 0,
            "next" => 1,
            "first" => 1,
            "third" => 3,
            "fourth" => 4,
            "fifth" => 5,
            "sixth" => 6,
            "seventh" => 7,
            "eighth" => 8,
            "ninth" => 9,
            "tenth" => 10,
            "eleventh" => 11,
            "twelfth" => 12,
            _ => unreachable!(),
        }
    }

    enum ParsedTimeUnit {
        Regular(u64),
        FuzzyMonth,
        FuzzyYear,
    }
    use ParsedTimeUnit::*;
    fn parse_time_unit(time_unit: &str) -> ParsedTimeUnit {
        match time_unit {
            "sec" | "secs" | "second" | "seconds" => Regular(1),
            "min" | "mins" | "minute" | "minutes" => Regular(60),
            "hour" | "hours" => Regular(60 * 60),
            "day" | "days" => Regular(24 * 60 * 60),
            "week" | "weeks" => Regular(7 * 24 * 60 * 60),
            "fortnight" | "fortnights" => Regular(2 * 7 * 24 * 60 * 60),
            "month" | "months" => FuzzyMonth,
            "year" | "years" => FuzzyYear,
            _ => unreachable!(),
        }
    }

    fn parse_keyword(keyword: &str) -> i64 {
        match keyword {
            "yesterday" => -(24 * 60 * 60),
            "tomorrow" => 24 * 60 * 60,
            "now" | "today" => 0,
            _ => unreachable!(),
        }
    }

    fn parse_fract(fract: &str) -> u64 {
        let mut nanos = 0;
        let mut multi = 100_000_000;
        for digit in fract.get(..fract.len().min(9)).unwrap().as_bytes() {
            nanos += (digit - b'0') as u64 * multi;
            multi /= 10;
        }
        nanos
    }

    for item in EXTRACTION_REGEX.captures_iter(input) {
        // Sort out durations which are empty besides or consist only of delimiter characters
        if let Some(duration) = item.name("duration").map(|m| m.as_str()) {
            if duration.trim_matches(DELIMITER_CHARS).is_empty() {
                continue;
            }
        }

        let mut is_negative = false;
        let mut whole_number = 1u64;
        let mut fract_number = 0u64;

        if let Some(sign) = item.name("sign").map(|m| m.as_str()) {
            is_negative = sign.eq("-")
        }
        if item.name("ago").map(|m| m.as_str()).is_some() {
            is_negative ^= true
        }

        if let (Some(whole), Some(fract)) = (item.name("whole"), item.name("fract")) {
            match whole.as_str().parse() {
                Ok(s) => {
                    whole_number = s;
                    fract_number = parse_fract(fract.as_str());
                }
                Err(_) => {
                    whole_number = u64::MAX;
                    fract_number = 999_999_999;
                }
            };
        }
        if let Some(whole) = item.name("number") {
            match whole.as_str().parse() {
                Ok(s) => whole_number = s,
                Err(_) => {
                    whole_number = u64::MAX;
                    fract_number = 999_999_999;
                }
            };
        }
        if let (Some(numeral), Some(time_unit)) =
            (item.name("numeral_value"), item.name("numeral_time_unit"))
        {
            let value = parse_numeral(numeral.as_str());
            match parse_time_unit(time_unit.as_str()) {
                Regular(m) => {
                    is_negative ^= value.is_negative();
                    whole_number = m * value.unsigned_abs()
                }
                FuzzyMonth if is_negative => {
                    months = months.saturating_sub(value);
                    whole_number = 0;
                    fract_number = 0;
                }
                FuzzyMonth => {
                    months = months.saturating_add(value);
                    whole_number = 0;
                    fract_number = 0;
                }
                FuzzyYear if is_negative => {
                    years = years.saturating_sub(value);
                    whole_number = 0;
                    fract_number = 0;
                }
                FuzzyYear => {
                    years = years.saturating_add(value);
                    whole_number = 0;
                    fract_number = 0;
                }
            }
        }
        if let Some(time_unit) = item.name("time_unit") {
            match parse_time_unit(time_unit.as_str()) {
                Regular(s) => match whole_number.checked_mul(s) {
                    Some(s) => whole_number = s,
                    None => {
                        whole_number = u64::MAX;
                        fract_number = 999_999_999;
                    }
                },
                FuzzyMonth if is_negative => {
                    let num = if whole_number >= i64::MIN.unsigned_abs() {
                        i64::MIN
                    } else {
                        (whole_number as i64).neg()
                    };
                    months = months.saturating_add(num);
                    whole_number = 0;
                    fract_number = 0;
                }
                FuzzyMonth => {
                    months = months.saturating_add(whole_number.try_into().unwrap_or(i64::MAX));
                    whole_number = 0;
                    fract_number = 0;
                }
                FuzzyYear if is_negative => {
                    let num = if whole_number >= i64::MIN.unsigned_abs() {
                        i64::MIN
                    } else {
                        (whole_number as i64).neg()
                    };
                    years = years.saturating_add(num);
                    whole_number = 0;
                    fract_number = 0;
                }
                FuzzyYear => {
                    years = years.saturating_add(whole_number.try_into().unwrap_or(i64::MAX));
                    whole_number = 0;
                    fract_number = 0;
                }
            }
        }
        if let Some(keyword) = item.name("keyword") {
            let s = parse_keyword(keyword.as_str());
            is_negative ^= s.is_negative();
            whole_number = s.unsigned_abs();
        }
        duration = duration.saturating_add(Duration::from_std(
            is_negative,
            StdDuration::new(whole_number, fract_number as u32),
        ));
    }

    (years, months, duration)
}

fuzz_target!(|input: &str| {
    let parser = RelativeTimeParser::new();
    let expect_success = REGEX.is_match(input);
    match parser.parse(input) {
        Ok(_) if expect_success => {
            // It is a pretty complex task to check the result of the [`RelativeTimeParser::parse`]
            // method directly. We're using [`RelativeTimeParser::parse_fuzzy`] instead, to verify
            // we've parsed the input string into the correct amount of `years`, `months` and the
            // [`Duration`]. The date calculations of the `parse` methods are tested very thoroughly
            // with unit and integration tests.
            let parsed = parser.parse_fuzzy(input).unwrap();
            let expected = extract(input);
            if parsed != expected {
                panic!(
                    "Results differ: expected {:?} != actual {:?}",
                    expected, parsed
                );
            }
        }
        Ok(duration) => {
            if input.starts_with(DELIMITER_CHARS)
                || input.ends_with(DELIMITER_CHARS)
                || CONTROL_REGEX.is_match(input)
            {
            } else {
                panic!("Expected an error but got a duration: {:?}", duration)
            }
        }
        Err(error) if expect_success => match &error {
            ParseError::InvalidInput(string)
                if (string == "Fraction without a whole number"
                    || string == "Fraction only allowed together with seconds as time unit")
                    && FRACTION_CONTROL_REGEX.is_match(input) => {}
            // Overflow errors cannot be checked with the grammar and main REGEX
            ParseError::Overflow => {}
            _ => {
                panic!("Expected a duration but got an error: {}", error)
            }
        },
        Err(_) => {}
    };
});
