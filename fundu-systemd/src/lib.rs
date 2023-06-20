// spell-checker: ignore econd inute onths nute nths econds inutes

//! TODO: DOCUMENT

#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc(test(attr(warn(unused))))]
#![doc(test(attr(allow(unused_extern_crates))))]
#![warn(missing_docs)]
#![warn(clippy::pedantic)]
#![warn(clippy::default_numeric_fallback)]
#![warn(clippy::else_if_without_else)]
#![warn(clippy::fn_to_numeric_cast_any)]
#![warn(clippy::get_unwrap)]
#![warn(clippy::if_then_some_else_none)]
#![warn(clippy::mixed_read_write_in_expression)]
#![warn(clippy::partial_pub_fields)]
#![warn(clippy::rest_pat_in_fully_bound_structs)]
#![warn(clippy::str_to_string)]
#![warn(clippy::string_to_string)]
#![warn(clippy::todo)]
#![warn(clippy::try_err)]
#![warn(clippy::undocumented_unsafe_blocks)]
#![warn(clippy::unneeded_field_pattern)]
#![allow(clippy::must_use_candidate)]
#![allow(clippy::return_self_not_must_use)]
#![allow(clippy::enum_glob_use)]
#![allow(clippy::module_name_repetitions)]

use fundu::TimeUnit::*;
use fundu::{
    Config, ConfigBuilder, Delimiter, Duration, Multiplier, ParseError, Parser, TimeUnit,
    TimeUnitsLike,
};

// whitespace definition of: b' ', b'\x09', b'\x0A', b'\x0B', b'\x0C', b'\x0D'
const DELIMITER: Delimiter = |byte| byte == b' ' || byte.wrapping_sub(9) < 5;

const CONFIG: Config = ConfigBuilder::new()
    .allow_delimiter(DELIMITER)
    .disable_exponent()
    .disable_infinity()
    .number_is_optional()
    .parse_multiple(DELIMITER, None)
    .build();

/// TODO: DOCUMENT
pub const TIME_UNITS_WITH_NANOS: TimeUnitsWithNanos = TimeUnitsWithNanos {};
/// TODO: DOCUMENT
pub const TIME_UNITS: TimeUnits = TimeUnits {};

const NANO_SECOND: (TimeUnit, Multiplier) = (NanoSecond, Multiplier(1, 0));
const MICRO_SECOND: (TimeUnit, Multiplier) = (MicroSecond, Multiplier(1, 0));
const MILLI_SECOND: (TimeUnit, Multiplier) = (MilliSecond, Multiplier(1, 0));
const SECOND: (TimeUnit, Multiplier) = (Second, Multiplier(1, 0));
const MINUTE: (TimeUnit, Multiplier) = (Minute, Multiplier(1, 0));
const HOUR: (TimeUnit, Multiplier) = (Hour, Multiplier(1, 0));
const DAY: (TimeUnit, Multiplier) = (Day, Multiplier(1, 0));
const WEEK: (TimeUnit, Multiplier) = (Week, Multiplier(1, 0));
const MONTH: (TimeUnit, Multiplier) = (Month, Multiplier(1, 0));
const YEAR: (TimeUnit, Multiplier) = (Year, Multiplier(1, 0));

const PARSER: TimeSpanParser<'static> = TimeSpanParser::new();

/// TODO: DOCUMENT
pub const SYSTEMD_MAX_USEC_DURATION: Duration =
    Duration::positive(u64::MAX / 1_000_000, (u64::MAX % 1_000_000) as u32 * 1000);
/// TODO: DOCUMENT
pub const SYSTEMD_MAX_NSEC_DURATION: Duration =
    Duration::positive(u64::MAX / 1_000_000_000, (u64::MAX % 1_000_000_000) as u32);

/// TODO: DOCUMENT
#[derive(Debug, Eq, PartialEq)]
pub struct TimeSpanParser<'a> {
    raw: Parser<'a>,
}

impl<'a> TimeSpanParser<'a> {
    /// TODO: DOCUMENT
    pub const fn new() -> Self {
        Self {
            raw: Parser::with_config(CONFIG),
        }
    }

    /// TODO: DOCUMENT
    pub const fn with_default_unit(time_unit: TimeUnit) -> Self {
        let mut config = CONFIG;
        config.default_unit = time_unit;
        Self {
            raw: Parser::with_config(config),
        }
    }

    fn parse_infinity(source: &str, max: Duration) -> Option<Duration> {
        (source == "infinity").then_some(max)
    }

    /// TODO: DOCUMENT
    ///
    /// # Errors
    pub fn parse(&self, source: &str) -> Result<Duration, ParseError> {
        self.parse_with_max(source, SYSTEMD_MAX_USEC_DURATION)
    }

    /// TODO: DOCUMENT
    ///
    /// # Panics
    ///
    /// # Errors
    pub fn parse_with_max(&self, source: &str, max: Duration) -> Result<Duration, ParseError> {
        assert!(max.is_positive());
        let trimmed = trim(source);
        match Self::parse_infinity(trimmed, max) {
            Some(duration) => Ok(duration),
            None => self
                .raw
                .parse(trimmed, &TIME_UNITS, None)
                .map(|duration| duration.min(max)),
        }
    }

    /// TODO: DOCUMENT
    ///
    /// # Errors
    pub fn parse_nanos(&self, source: &str) -> Result<Duration, ParseError> {
        self.parse_nanos_with_max(source, SYSTEMD_MAX_NSEC_DURATION)
    }

    /// TODO: DOCUMENT
    ///
    /// # Panics
    ///
    /// # Errors
    pub fn parse_nanos_with_max(
        &self,
        source: &str,
        max: Duration,
    ) -> Result<Duration, ParseError> {
        assert!(max.is_positive());
        let trimmed = trim(source);
        match Self::parse_infinity(trimmed, max) {
            Some(duration) => Ok(duration),
            None => self
                .raw
                .parse(trimmed, &TIME_UNITS_WITH_NANOS, None)
                .map(|duration| duration.min(max)),
        }
    }

    /// TODO: DOCUMENT
    pub fn set_default_unit(&mut self, time_unit: TimeUnit) {
        self.raw.config.default_unit = time_unit;
    }
}

impl<'a> Default for TimeSpanParser<'a> {
    fn default() -> Self {
        Self::new()
    }
}

/// TODO: DOCUMENT
pub struct TimeUnits {}

impl TimeUnitsLike for TimeUnits {
    #[inline]
    fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        match identifier {
            // These are two different letters: the greek small letter mu U+03BC and the micro sign
            // U+00B5
            "us" | "\u{03bc}s" | "\u{00b5}s" | "usec" => Some(MICRO_SECOND),
            "ms" | "msec" => Some(MILLI_SECOND),
            "s" | "sec" | "second" | "seconds" => Some(SECOND),
            "m" | "min" | "minute" | "minutes" => Some(MINUTE),
            "h" | "hr" | "hour" | "hours" => Some(HOUR),
            "d" | "day" | "days" => Some(DAY),
            "w" | "week" | "weeks" => Some(WEEK),
            "M" | "month" | "months" => Some(MONTH),
            "y" | "year" | "years" => Some(YEAR),
            _ => None,
        }
    }
}

/// TODO: DOCUMENT
pub struct TimeUnitsWithNanos {}

impl TimeUnitsLike for TimeUnitsWithNanos {
    #[inline]
    fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    fn get(&self, identifier: &str) -> Option<(TimeUnit, Multiplier)> {
        match identifier {
            "ns" | "nsec" => Some(NANO_SECOND),
            // These are two different letters: the greek small letter mu U+03BC and the micro sign
            // U+00B5
            "us" | "\u{03bc}s" | "\u{00b5}s" | "usec" => Some(MICRO_SECOND),
            "ms" | "msec" => Some(MILLI_SECOND),
            "s" | "sec" | "second" | "seconds" => Some(SECOND),
            "m" | "min" | "minute" | "minutes" => Some(MINUTE),
            "h" | "hr" | "hour" | "hours" => Some(HOUR),
            "d" | "day" | "days" => Some(DAY),
            "w" | "week" | "weeks" => Some(WEEK),
            "M" | "month" | "months" => Some(MONTH),
            "y" | "year" | "years" => Some(YEAR),
            _ => None,
        }
    }
}

/// TODO: DOCUMENT
///
/// # Errors
pub fn parse(
    source: &str,
    default_unit: Option<TimeUnit>,
    max: Option<Duration>,
) -> Result<Duration, ParseError> {
    match default_unit {
        None | Some(TimeUnit::Second) => {
            PARSER.parse_with_max(source, max.unwrap_or(SYSTEMD_MAX_USEC_DURATION))
        }
        Some(time_unit) => {
            let mut parser = PARSER;
            parser.set_default_unit(time_unit);
            parser.parse_with_max(source, max.unwrap_or(SYSTEMD_MAX_USEC_DURATION))
        }
    }
}

/// TODO: DOCUMENT
///
/// # Errors
pub fn parse_nanos(
    source: &str,
    default_unit: Option<TimeUnit>,
    max: Option<Duration>,
) -> Result<Duration, ParseError> {
    match default_unit {
        None | Some(TimeUnit::Second) => {
            PARSER.parse_nanos_with_max(source, max.unwrap_or(SYSTEMD_MAX_NSEC_DURATION))
        }
        Some(time_unit) => {
            let mut parser = PARSER;
            parser.set_default_unit(time_unit);
            parser.parse_nanos_with_max(source, max.unwrap_or(SYSTEMD_MAX_NSEC_DURATION))
        }
    }
}

// This is a faster alternative to str::trim_matches. We're exploiting that we're using the posix
// definition of whitespace which only contains ascii characters as whitespace
fn trim(source: &str) -> &str {
    let mut bytes = source.as_bytes();
    while let Some((byte, remainder)) = bytes.split_first() {
        if byte == &b' ' || byte.wrapping_sub(9) < 5 {
            bytes = remainder;
        } else {
            break;
        }
    }
    while let Some((byte, remainder)) = bytes.split_last() {
        if byte == &b' ' || byte.wrapping_sub(9) < 5 {
            bytes = remainder;
        } else {
            break;
        }
    }
    // SAFETY: We've trimmed only ascii characters and therefore valid utf-8
    unsafe { std::str::from_utf8_unchecked(bytes) }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;

    #[test]
    fn test_parser_new() {
        let parser = TimeSpanParser::new();
        assert_eq!(parser.raw.config, CONFIG);
    }

    #[rstest]
    #[case::not_second(TimeUnit::Week)]
    #[case::second(TimeUnit::Second)]
    fn test_parser_with_default_unit(#[case] time_unit: TimeUnit) {
        let parser = TimeSpanParser::with_default_unit(time_unit);
        let mut config = CONFIG;
        config.default_unit = time_unit;
        assert_eq!(parser.raw.config, config);
    }

    #[rstest]
    #[case::not_second(TimeUnit::Week)]
    #[case::second(TimeUnit::Second)]
    fn test_parser_set_default_unit(#[case] time_unit: TimeUnit) {
        let mut config = CONFIG;
        config.default_unit = time_unit;

        let mut parser = TimeSpanParser::new();
        parser.set_default_unit(time_unit);

        assert_eq!(parser.raw.config, config);
    }

    #[test]
    fn test_parser_default() {
        assert_eq!(TimeSpanParser::new(), TimeSpanParser::default());
        assert_eq!(TimeSpanParser::default(), PARSER);
    }

    #[rstest]
    #[case::time_units(&TimeUnits {})]
    #[case::time_units_with_nanos(&TimeUnitsWithNanos {})]
    fn test_time_units_is_not_empty(#[case] time_units_like: &dyn TimeUnitsLike) {
        assert!(!time_units_like.is_empty());
    }
}
