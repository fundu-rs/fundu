// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use crate::time::{Multiplier, DEFAULT_TIME_UNIT};
use crate::TimeUnit;

pub(crate) const DEFAULT_CONFIG: Config = Config::new();

/// An ascii delimiter defined as closure.
///
/// The [`Delimiter`] is a type alias for a closure taking a `u8` byte and returning a `bool`. Most
/// likely, the [`Delimiter`] is used to define some whitespace but whitespace definitions differ,
/// so a closure provides the most flexible definition of a delimiter. For example the definition of
/// whitespace from rust [`u8::is_ascii_whitespace`]:
///
/// ```text
/// Checks if the value is an ASCII whitespace character: U+0020 SPACE, U+0009 HORIZONTAL TAB,
/// U+000A LINE FEED, U+000C FORM FEED, or U+000D CARRIAGE RETURN.
///
/// Rust uses the WhatWG Infra Standard’s definition of ASCII whitespace. There are several other
/// definitions in wide use. For instance, the POSIX locale includes U+000B VERTICAL TAB as well
/// as all the above characters, but—from the very same specification—the default rule for “field
/// splitting” in the Bourne shell considers only SPACE, HORIZONTAL TAB, and LINE FEED as
/// whitespace.
/// ```
///
/// # Problems
///
/// The delimiter takes a `u8` as input, but matching any non-ascii (`0x80 - 0xff`) bytes may lead
/// to a [`crate::ParseError`] if the input string contains multi-byte utf-8 characters.
///
/// # Examples
///
/// ```rust
/// use fundu::Delimiter;
///
/// fn is_delimiter(delimiter: Delimiter, byte: u8) -> bool {
///     delimiter(byte)
/// }
///
/// assert!(is_delimiter(
///     |byte| matches!(byte, b' ' | b'\n' | b'\t'),
///     b' '
/// ));
/// assert!(!is_delimiter(
///     |byte| matches!(byte, b' ' | b'\n' | b'\t'),
///     b'\r'
/// ));
/// assert!(is_delimiter(|byte| byte.is_ascii_whitespace(), b'\r'));
/// ```
pub type Delimiter = fn(u8) -> bool;

#[derive(Debug, PartialEq, Eq, Clone)]
#[allow(clippy::struct_excessive_bools)]
pub(crate) struct Config<'a> {
    pub(crate) allow_delimiter: Option<Delimiter>,
    pub(crate) default_unit: TimeUnit,
    pub(crate) default_multiplier: Multiplier,
    pub(crate) disable_exponent: bool,
    pub(crate) disable_fraction: bool,
    pub(crate) disable_infinity: bool,
    pub(crate) number_is_optional: bool,
    pub(crate) max_exponent: i16,
    pub(crate) min_exponent: i16,
    pub(crate) parse_multiple_delimiter: Option<Delimiter>,
    pub(crate) parse_multiple_conjunctions: Option<&'a [&'a str]>,
    pub(crate) allow_negative: bool,
    pub(crate) allow_ago: Option<Delimiter>,
}

impl<'a> Default for Config<'a> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> Config<'a> {
    pub(crate) const fn new() -> Self {
        Self {
            allow_delimiter: None,
            default_unit: DEFAULT_TIME_UNIT,
            default_multiplier: Multiplier(1, 0),
            disable_exponent: false,
            disable_fraction: false,
            number_is_optional: false,
            max_exponent: i16::MAX,
            min_exponent: i16::MIN,
            disable_infinity: false,
            parse_multiple_delimiter: None,
            parse_multiple_conjunctions: None,
            allow_negative: false,
            allow_ago: None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_for_config() {
        assert_eq!(Config::default(), Config::new());
    }
}
