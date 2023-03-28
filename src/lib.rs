// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! # Overview
//!
//! Parse a rust string into a [`std::time::Duration`] or for negative numbers into a
//! [`time::Duration`].
//!
//! `fundu` is a configurable, precise and blazingly fast string parser
//!
//! * with the flexibility to customize [`TimeUnit`]s, the number format and other aspects
//! * without floating point calculations. What you put in is what you get out.
//! * with sound limit handling. Infinity and numbers larger than [`Duration::MAX`] evaluate to
//! [`Duration::MAX`]. Numbers `x` with `abs(x) < 1e-18` evaluate to [`Duration::ZERO`].
//! * with the option to parse negative numbers to negative durations if the `negative` feature is
//! enabled
//! * and with informative error messages
//!
//! # Features
//!
//! ## `standard`
//!
//! The `standard` feature exposes the [`DurationParser`] and [`DurationParserBuilder`] structs with
//! time units which can be customized. However, the `identifier` for each [`TimeUnit`] is fixed.
//!
//! ## `custom`
//!
//! The `custom` feature provides a [`CustomDurationParser`] with fully customizable identifiers for
//! each [`TimeUnit`]. With the [`CustomDurationParser`] it is also possible to define completely
//! new time units, a [`CustomTimeUnit`].
//!
//! ## `negative`
//!
//! Enable parsing negative numbers into negative durations represented by [`time::Duration`]
//! (instead of a [`std::time::Duration`]). If not activated, negative numbers produce a
//! [`ParseError::NegativeNumber`].
//!
//! # Configuration and Format
//!
//! This parser can be configured to accept strings with a default set of time units
//! [`DurationParser::new`], with all time units [`DurationParser::with_all_time_units`] or
//! without [`DurationParser::without_time_units`]. A custom set of time units is also possible with
//! [`DurationParser::with_time_units`]. All these parsers accept strings such as
//!
//! * `1.41`
//! * `42`
//! * `2e-8`, `2e+8` (or likewise `2.0e8`)
//! * `.5` or likewise `0.5`
//! * `3.` or likewise `3.0`
//! * `inf`, `+inf`, `infinity`, `+infinity`
//!
//! All alphabetic characters are matched case-insensitive, so `InFINity` or `2E8` are valid input
//! strings. Additionally, depending on the chosen set of time units one of the following time units
//! (the first column) are accepted.
//!
//! | [`TimeUnit`]    | default id | is default time unit
//! | --------------- | ----------:|:--------------------:
//! | [`Nanosecond`]  |         ns | yes
//! | [`Microsecond`] |         Ms | yes
//! | [`Millisecond`] |         ms | yes
//! | [`Second`]      |          s | yes
//! | [`Minute`]      |          m | yes
//! | [`Hour`]        |          h | yes
//! | [`Day`]         |          d | yes
//! | [`Week`]        |          w | yes
//! | [`Month`]       |          M |  no
//! | [`Year`]        |          y |  no
//!
//! If no time unit is given and not specified otherwise with [`DurationParser::default_unit`] then
//! `s` (= [`Second`]) is assumed. Some accepted strings with time units
//!
//! * `31.2s`
//! * `200000Ms`
//! * `3.14e8w`
//! * ...
//!
//! Per default there is no whitespace allowed between the number and the [`TimeUnit`], but this
//! behavior can be changed with setting [`DurationParser::allow_delimiter`].
//!
//! # Format specification
//!
//! The time units are case-sensitive, all other alphabetic characters are case-insensitive
//!
//! ```text
//! Duration ::= Sign? ( 'inf' | 'infinity' | ( Number TimeUnit?))
//! TimeUnit ::= ns | Ms | ms | s | m | h | d | w | M | y
//! Number   ::= ( Digit+ |
//!                Digit+ '.' Digit* |
//!                Digit* '.' Digit+ )
//!              Exp?
//! Exp      ::= 'e' Sign? Digit+
//! Sign     ::= [+-]
//! Digit    ::= [0-9]
//! ```
//!
//! Special cases which are not displayed in the specification:
//!
//! * The `TimeUnit` rule is based on the default identifiers as defined in the table above. They
//!   can also be completely customized with the [`CustomDurationParser`].
//! * Negative values, including negative infinity are not allowed. For exceptions see the next
//!   point.
//! * Numbers `x` (positive and negative) close to `0` (`abs(x) < 1e-18`) are treated as `0`
//! * Positive infinity and numbers exceeding [`Duration::MAX`] saturate at [`Duration::MAX`]
//! * The exponent must be in the range `-32768 <= Exp <= 32767`
//! * If `allow_delimiter` is set then any defined delimiter is allowed between the Number and
//! TimeUnit. This setting also allows the input string to end with this delimiter but only if no
//! time unit was present. The parser then assumes the default time unit.
//!
//! # Examples
//!
//! If only the default configuration is required once, the [`parse_duration`] method can be used.
//!
//! ```rust
//! use std::time::Duration;
//!
//! use fundu::parse_duration;
//!
//! let input = "1.0e2s";
//! assert_eq!(parse_duration(input).unwrap(), Duration::new(100, 0));
//! ```
//!
//! When a customization of the accepted [`TimeUnit`]s is required, then the builder
//! [`DurationParser`] can be used.
//!
//! ```rust
//! use std::time::Duration;
//!
//! use fundu::DurationParser;
//!
//! let input = "3m";
//! assert_eq!(
//!     DurationParser::with_all_time_units().parse(input).unwrap(),
//!     Duration::new(180, 0)
//! );
//! ```
//!
//! When no time units are configured, seconds is assumed.
//!
//! ```rust
//! use std::time::Duration;
//!
//! use fundu::DurationParser;
//!
//! let input = "1.0e2";
//! assert_eq!(
//!     DurationParser::without_time_units().parse(input).unwrap(),
//!     Duration::new(100, 0)
//! );
//! ```
//!
//! However, the following will return an error because `y` (Years) is not a default time unit:
//!
//! ```rust
//! use fundu::DurationParser;
//!
//! let input = "3y";
//! assert!(DurationParser::new().parse(input).is_err());
//! ```
//!
//! The parser is reusable and the set of time units is fully customizable
//!
//! ```rust
//! use std::time::Duration;
//!
//! use fundu::DurationParser;
//! use fundu::TimeUnit::*;
//!
//! let parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);
//! for (input, expected) in &[
//!     ("9e3ns", Duration::new(0, 9000)),
//!     ("10m", Duration::new(600, 0)),
//!     ("1.1h", Duration::new(3960, 0)),
//!     ("7", Duration::new(7, 0)),
//! ] {
//!     assert_eq!(parser.parse(input).unwrap(), *expected);
//! }
//! ```
//!
//! Setting the default time unit (if no time unit is given in the input string) to something
//! different than seconds is also easily possible
//!
//! ```rust
//! use std::time::Duration;
//!
//! use fundu::DurationParser;
//! use fundu::TimeUnit::*;
//!
//! assert_eq!(
//!     DurationParser::without_time_units()
//!         .default_unit(MilliSecond)
//!         .parse("1000")
//!         .unwrap(),
//!     Duration::new(1, 0)
//! );
//! ```
//! The identifiers for time units can be fully customized with any number of valid
//! [utf-8](https://en.wikipedia.org/wiki/UTF-8) sequences if the `custom` feature is activated:
//!
//! ```rust
//! use std::time::Duration;
//!
//! use fundu::CustomDurationParser;
//! use fundu::TimeUnit::*;
//!
//! let parser = CustomDurationParser::with_time_units(&[
//!     (MilliSecond, &["χιλιοστό του δευτερολέπτου"]),
//!     (Second, &["s", "secs"]),
//!     (Hour, &["⏳"]),
//! ]);
//! for (input, expected) in &[
//!     (".3χιλιοστό του δευτερολέπτου", Duration::new(0, 300_000)),
//!     ("1e3secs", Duration::new(1000, 0)),
//!     ("1.1⏳", Duration::new(3960, 0)),
//! ] {
//!     assert_eq!(parser.parse(input).unwrap(), *expected);
//! }
//! ```
//!
//! Also, `fundu` tries to give informative error messages
//!
//! ```rust
//! use std::time::Duration;
//!
//! use fundu::DurationParser;
//!
//! assert_eq!(
//!     DurationParser::without_time_units()
//!         .parse("1y")
//!         .unwrap_err()
//!         .to_string(),
//!     "Time unit error: No time units allowed but found: 'y' at column 1"
//! );
//! ```
//!
//! The number format can be easily adjusted to your needs. For example to allow numbers being
//! optional, allow some ascii whitespace between the number and the time unit and restrict the
//! number format to whole numbers, without fractional part and an exponent:
//!
//! ```rust
//! use std::time::Duration;
//!
//! use fundu::TimeUnit::*;
//! use fundu::{DurationParser, ParseError};
//!
//! let parser = DurationParser::builder()
//!     .custom_time_units(&[NanoSecond])
//!     .allow_delimiter(|byte| matches!(byte, b'\t' | b'\n' | b'\r' | b' '))
//!     .number_is_optional()
//!     .disable_fraction()
//!     .disable_exponent()
//!     .build();
//!
//! for (input, expected) in &[
//!     ("ns", Duration::new(0, 1)),
//!     ("1000\t\n\r ns", Duration::new(0, 1000)),
//! ] {
//!     assert_eq!(parser.parse(input).unwrap(), *expected);
//! }
//!
//! for (input, expected) in &[
//!     (
//!         "1.0ns",
//!         ParseError::Syntax(1, "No fraction allowed".to_string()),
//!     ),
//!     (
//!         "1e9ns",
//!         ParseError::Syntax(1, "No exponent allowed".to_string()),
//!     ),
//! ] {
//!     assert_eq!(parser.parse(input).unwrap_err(), *expected);
//! }
//! ```
//!
//! [`time::Duration`]: <https://docs.rs/time/latest/time/struct.Duration.html>
//! [`Duration::MAX`]: [`std::Duration::MAX`]
//! [`Duration::ZERO`]: [`std::Duration::ZERO`]
//! [`NanoSecond`]: [`TimeUnit::NanoSecond`]
//! [`MicroSecond`]: [`TimeUnit::MicroSecond`]
//! [`MilliSecond`]: [`TimeUnit::MilliSecond`]
//! [`Second`]: [`TimeUnit::Second`]
//! [`Minute`]: [`TimeUnit::Minute`]
//! [`Hour`]: [`TimeUnit::Hour`]
//! [`Day`]: [`TimeUnit::Day`]
//! [`Week`]: [`TimeUnit::Week`]
//! [`Month`]: [`TimeUnit::Month`]
//! [`Year`]: [`TimeUnit::Year`]

#![cfg_attr(docsrs, feature(doc_auto_cfg))]

mod builder;
mod error;
mod parse;
mod time;

use builder::config;
#[cfg(feature = "custom")]
pub use builder::custom::{
    CustomDurationParser, CustomDurationParserBuilder, CustomTimeUnit, DEFAULT_ALL_TIME_UNITS,
    DEFAULT_TIME_UNITS, SYSTEMD_TIME_UNITS,
};
#[cfg(feature = "standard")]
pub use builder::standard::{parse_duration, DurationParser, DurationParserBuilder};
pub use config::Delimiter;
pub use error::ParseError;

pub use crate::time::{
    Multiplier, TimeUnit, DEFAULT_ID_DAY, DEFAULT_ID_HOUR, DEFAULT_ID_MICRO_SECOND,
    DEFAULT_ID_MILLI_SECOND, DEFAULT_ID_MINUTE, DEFAULT_ID_MONTH, DEFAULT_ID_NANO_SECOND,
    DEFAULT_ID_SECOND, DEFAULT_ID_WEEK, DEFAULT_ID_YEAR,
};
