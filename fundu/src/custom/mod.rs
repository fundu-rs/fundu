// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu_core::config::NumbersLike;
use fundu_core::time::Multiplier;

pub(crate) mod builder;
pub(crate) mod parser;
pub(crate) mod time_units;

/// A [`Numeral`] can occur where numbers usually occur in the source string
///
/// `Numerals` express a number as a word like `one` or `next` instead of `1` or `half` instead of
/// `0.5` but also `last` instead of `-1` etc. This symbolic number is defined as a [`Multiplier`].
/// In contrast to numbers, `Numerals` without a time unit are considered an error and therefore
/// have to be followed by a time unit.
///
/// # Examples
///
/// ```rust
/// use fundu::TimeUnit::*;
/// use fundu::{CustomDurationParserBuilder, CustomTimeUnit, Duration, Multiplier, Numeral};
///
/// let parser = CustomDurationParserBuilder::new()
///     .numerals(&[
///         Numeral::new(&["last"], Multiplier(-1, 0)),
///         Numeral::new(&["this"], Multiplier(0, 0)),
///         Numeral::new(&["one", "next"], Multiplier(1, 0)),
///         Numeral::new(&["two"], Multiplier(2, 0)),
///     ])
///     .time_unit(CustomTimeUnit::with_default(NanoSecond, &["nano", "nanos"]))
///     .allow_negative()
///     .build();
///
/// assert_eq!(parser.parse("last nano"), Ok(Duration::negative(0, 1)));
/// assert_eq!(parser.parse("this nano"), Ok(Duration::negative(0, 0)));
/// assert_eq!(parser.parse("next nano"), Ok(Duration::positive(0, 1)));
/// assert_eq!(parser.parse("two nanos"), Ok(Duration::positive(0, 2)));
/// ```
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Numeral<'a> {
    identifiers: &'a [&'a str],
    multiplier: Multiplier,
}

impl<'a> Numeral<'a> {
    /// Create a new [`Numeral`]
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use fundu::Numeral;
    ///
    /// let numeral = Numeral::new(&["next", "one"], Multiplier(1, 0));
    /// ```
    pub fn new(identifiers: &'a [&'a str], multiplier: Multiplier) -> Self {
        Self {
            identifiers,
            multiplier,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Numerals<'a> {
    data: Vec<Numeral<'a>>,
}

impl<'a> Numerals<'a> {
    pub(crate) fn new() -> Self {
        Self { data: vec![] }
    }

    pub(crate) fn with_numerals(numerals: Vec<Numeral<'a>>) -> Self {
        Self { data: numerals }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

impl<'a> NumbersLike for Numerals<'a> {
    fn get(&self, input: &str) -> Option<Multiplier> {
        self.data.iter().find_map(|numeral| {
            numeral
                .identifiers
                .iter()
                .find_map(|id| (*id == input).then_some(numeral.multiplier))
        })
    }
}
