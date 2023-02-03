// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! # Overview
//!
//! `fundu` provides a duration parser to parse strings into a [`std::time::Duration`]. It tries
//! to improve on the standard method `Duration::from_secs_f64(input.parse().unwrap())` by
//!
//! * Providing customizable [`TimeUnit`]s which are accepted in the input string. See table below.
//! * Using no floating point calculations and precisely parse the input as it is. So, what you put
//! in you is what you get out within the range of a [`std::time::Duration`].
//! * Evaluating to [`std::time::Duration::MAX`] if the input number was larger than that maximum or
//! the input string was positive `infinity`
//! * Providing better error messages in case of parsing errors.
//!
//! These features come with almost no additional runtime costs by still being a lightweight crate.
//! This crate is built on top of the rust `stdlib`, so no additional dependencies are required. The
//! accepted number format is very close to the scientific floating point format. See the format
//! specification below for details.
//!
//! # Examples
//!
//! If only the default configuration is required, the [`parse_duration`] method can be used.
//!
//! ```rust
//! use fundu::parse_duration;
//! use std::time::Duration;
//!
//! let input = "1.0e2s";
//! assert_eq!(parse_duration(input).unwrap(), Duration::new(100, 0));
//! ```
//!
//! When a customization of the accepted [`TimeUnit`] is required, then the builder
//! [`DurationParser`] can be used.
//!
//! ```rust
//! use fundu::DurationParser;
//! use std::time::Duration;
//!
//! let input = "3m";
//! assert_eq!(DurationParser::with_all_time_units().parse(input).unwrap(), Duration::new(180, 0));
//! ```
//!
//! When no time units are configured, seconds is assumed.
//!
//! ```rust
//! use fundu::DurationParser;
//! use std::time::Duration;
//!
//! let input = "1.0e2";
//! assert_eq!(DurationParser::without_time_units().parse(input).unwrap(), Duration::new(100, 0));
//! ```
//!
//! However, this will return an error because `y` (Years) is not a default time unit.
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
//! use fundu::{DurationParser, TimeUnit::*};
//! use std::time::Duration;
//!
//! let mut parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);
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
//! Also, `fundu` tries to give informative error messages
//!
//! ```rust
//! use fundu::DurationParser;
//! use std::time::Duration;
//!
//! assert_eq!(
//!     DurationParser::without_time_units()
//!         .parse("1y")
//!         .unwrap_err()
//!         .to_string(),
//!     "Syntax error: No time units allowed but found: y at column 1"
//! );
//! ```
//!
//! # Format specification
//!
//! ```text
//! Duration ::= Sign?                                       # No negative values besides negative zero
//!              ( 'inf' | 'infinity' | Number )             # 'inf' and 'infinity' are case insensitive
//! TimeUnit ::= ns | Ms | ms | s | m | h | d | w | M | y    # The accepted units are customizable
//! Number   ::= ( Digit+ |
//!                Digit+ '.' Digit* |
//!                Digit* '.' Digit+ )
//!               Exp?                                       # -1022 <= EXP <= 1023
//!               TimeUnit?                                  # If no time unit then seconds is assumed
//! Exp      ::= [eE] Sign? Digit+
//! Sign     ::= [+-]
//! Digit    ::= [0-9]
//! ```

mod error;
mod time;

use std::cmp::Ordering;
use std::slice::Iter;
use std::time::Duration;

pub use error::ParseError;
pub use time::TimeUnit;
use time::TimeUnits;
pub use time::{
    DEFAULT_ID_DAY, DEFAULT_ID_HOUR, DEFAULT_ID_MICRO_SECOND, DEFAULT_ID_MILLI_SECOND,
    DEFAULT_ID_MINUTE, DEFAULT_ID_MONTH, DEFAULT_ID_NANO_SECOND, DEFAULT_ID_SECOND,
    DEFAULT_ID_WEEK, DEFAULT_ID_YEAR,
};

const ATTO_MULTIPLIER: u64 = 1_000_000_000_000_000_000;
const ATTO_TO_NANO: u64 = 1_000_000_000;

/// An intermediate representation of seconds.
///
/// Optionally append `usize` amount of zeroes.
struct Seconds<'a>(Option<&'a [u8]>, Option<&'a [u8]>, Option<usize>);

impl<'a> Seconds<'a> {
    const ZERO: Self = Seconds(None, None, None);

    fn parse(&self) -> Result<u64, ParseError> {
        let mut seconds: u64 = 0;
        // 20 is the number of digits of u64::MAX
        let num_zeroes = self.2.unwrap_or(0).min(20);

        for c in self
            .0
            .iter()
            .flat_map(|s| s.iter())
            .chain(self.1.iter().flat_map(|s| s.iter()))
            .chain((0..num_zeroes).map(|_| &0u8))
        {
            match seconds
                .checked_mul(10)
                .and_then(|s| s.checked_add(*c as u64))
            {
                Some(s) => seconds = s,
                None => {
                    return Err(ParseError::Overflow);
                }
            }
        }

        Ok(seconds)
    }
}

/// An intermediate representation of atto seconds.
///
/// Optionally prepend `usize` amount of zeroes.
struct Attos<'a>(Option<usize>, Option<&'a [u8]>, Option<&'a [u8]>);

impl<'a> Attos<'a> {
    const ZERO: Self = Attos(None, None, None);

    fn parse(&self) -> u64 {
        let mut multi = ATTO_MULTIPLIER / 10;
        let mut attos: u64 = 0;

        // 10 is the number of digits of atto seconds
        let num_zeroes = self.0.unwrap_or(0).min(18);

        for c in (0..num_zeroes)
            .map(|_| &0)
            .chain(self.1.iter().flat_map(|s| s.iter()))
            .chain(self.2.iter().flat_map(|s| s.iter()))
            .take(18)
        {
            attos += *c as u64 * multi;
            multi /= 10;
        }

        attos
    }
}

#[derive(Debug, Default)]
struct DurationRepr {
    is_negative: bool,
    is_infinite: bool,
    whole: Option<Vec<u8>>,
    fract: Option<Vec<u8>>,
    exponent: i16,
    unit: TimeUnit,
}

impl DurationRepr {
    fn parse(&mut self) -> Result<Duration, ParseError> {
        if self.is_infinite {
            if self.is_negative {
                return Err(ParseError::InvalidInput("Negative infinity".to_string()));
            } else {
                return Ok(Duration::MAX);
            }
        }

        let (whole, fract) = match (self.whole.take(), self.fract.take()) {
            (None, None) => unreachable!("Must be handled when parsing from string."),
            (None, Some(fract)) => (vec![], fract),
            (Some(whole), None) => (whole, vec![]),
            (Some(whole), Some(fract)) => (whole, fract),
        };

        self.exponent -= match self.unit {
            TimeUnit::NanoSecond
            | TimeUnit::MicroSecond
            | TimeUnit::MilliSecond
            | TimeUnit::Second => self.unit.multiplier().try_into().unwrap(), // unwrap is safe here because multiplier is max == 9
            _ => 0,
        };

        // The maximum absolute value of the exponent is `1023`, so it is safe to cast to usize
        let exponent_abs: usize = self.exponent.unsigned_abs().into();

        // We're operating on slices to minimize runtime costs. Applying the exponent before parsing
        // to integers is necessary, since the exponent can move digits into the to be considered
        // final integer domain.
        let (seconds, attos) = match self.exponent.cmp(&0) {
            Ordering::Less if whole.len() > exponent_abs => {
                let seconds = Seconds(Some(&whole[..whole.len() - exponent_abs]), None, None);
                let attos = Attos(
                    None,
                    Some(&whole[whole.len() - exponent_abs..]),
                    Some(&fract),
                );
                (seconds, attos)
            }
            Ordering::Less => {
                let seconds = Seconds::ZERO;
                let attos = Attos(Some(exponent_abs - whole.len()), Some(&whole), Some(&fract));
                (seconds, attos)
            }
            Ordering::Equal => {
                let seconds = Seconds(Some(&whole), None, None);
                let attos = Attos(None, Some(&fract), None);
                (seconds, attos)
            }
            Ordering::Greater if fract.len() > exponent_abs => {
                let seconds = Seconds(Some(&whole), Some(&fract[..exponent_abs]), None);
                let attos = Attos(None, Some(&fract[exponent_abs..]), None);
                (seconds, attos)
            }
            Ordering::Greater => {
                let seconds = Seconds(Some(&whole), Some(&fract), Some(exponent_abs - fract.len()));
                let attos = Attos::ZERO;
                (seconds, attos)
            }
        };

        // Finally, parse the seconds and atto seconds and interpret a seconds overflow as
        // maximum `Duration`.
        let (seconds, attos) = match seconds.parse() {
            Ok(seconds) => (seconds, attos.parse()),
            Err(ParseError::Overflow) => return Ok(Duration::MAX),
            Err(_) => unreachable!(), // only ParseError::Overflow is returned by `Seconds::parse`
        };

        // allow `-0` or `-0.0` and interpret as plain `0`
        if self.is_negative && seconds == 0 && attos == 0 {
            Ok(Duration::ZERO)
        } else if self.is_negative {
            Err(ParseError::InvalidInput("Negative number".to_string()))
        } else {
            match self.unit {
                TimeUnit::NanoSecond
                | TimeUnit::MicroSecond
                | TimeUnit::MilliSecond
                | TimeUnit::Second => Ok(Duration::new(seconds, (attos / ATTO_TO_NANO) as u32)),
                TimeUnit::Minute
                | TimeUnit::Hour
                | TimeUnit::Day
                | TimeUnit::Week
                | TimeUnit::Month
                | TimeUnit::Year => {
                    let attos = attos as u128 * (self.unit.multiplier() as u128);
                    Ok(
                        match seconds
                            .checked_mul(self.unit.multiplier())
                            .and_then(|s| s.checked_add((attos / (ATTO_MULTIPLIER as u128)) as u64))
                        {
                            Some(s) => Duration::new(
                                s,
                                ((attos / (ATTO_TO_NANO as u128)) % 1_000_000_000) as u32,
                            ),
                            None => Duration::MAX,
                        },
                    )
                }
            }
        }
    }
}

struct ReprParser<'a> {
    current_byte: Option<&'a u8>,
    current_pos: usize,
    iterator: Iter<'a, u8>,
    time_units: &'a TimeUnits<'a>,
}

/// Parse a source string into a [`DurationRepr`].
impl<'a> ReprParser<'a> {
    fn new(input: &'a str, time_units: &'a TimeUnits) -> Self {
        let mut iterator = input.as_bytes().iter();
        Self {
            current_byte: iterator.next(),
            current_pos: 0,
            iterator,
            time_units,
        }
    }

    fn advance(&mut self) {
        self.current_byte = self.iterator.next();
        self.current_pos += 1;
    }

    fn parse(&mut self) -> Result<DurationRepr, ParseError> {
        let mut duration_repr = DurationRepr::default();

        // parse the sign if present
        if self.parse_sign_is_negative()? {
            duration_repr.is_negative = true;
        }

        // parse infinity or the whole number part of the input
        match self.current_byte {
            Some(byte) if *byte == b'i' || *byte == b'I' => {
                self.parse_infinity()?;
                duration_repr.is_infinite = true;
                return Ok(duration_repr);
            }
            Some(byte) if byte.is_ascii_digit() => {
                // the maximum number of digits that need to be considered:
                // max(-exponent) = 1022 + max_digits(u64::MAX) = 20 + 1
                let whole = self.parse_digits(1043, true)?;
                duration_repr.whole = Some(whole);
            }
            Some(byte) if *byte == b'.' => {}
            Some(byte) => {
                return Err(ParseError::Syntax(
                    self.current_pos,
                    format!(
                        "Invalid character: {}",
                        std::str::from_utf8(&[*byte]).unwrap_or("invalid utf8")
                    ),
                ))
            }
            None => {
                return Err(ParseError::Syntax(
                    self.current_pos,
                    "Unexpected end of input".to_string(),
                ))
            }
        }

        // parse the fraction number part of the input
        match self.current_byte {
            Some(byte) if *byte == b'.' => {
                self.advance();
                let fract = match self.current_byte {
                    // the maximum number of digits that need to be considered:
                    // max(+exponent) = 1023 + max_digits(nano seconds) = 9 + 1
                    Some(byte) if byte.is_ascii_digit() => Some(self.parse_digits(1033, false)?),
                    Some(_) if duration_repr.whole.is_none() => {
                        return Err(ParseError::Syntax(
                            self.current_pos,
                            "Either the whole number part or the fraction must be present"
                                .to_string(),
                        ))
                    }
                    Some(_) => None,
                    None => return Ok(duration_repr),
                };
                duration_repr.fract = fract;
            }
            Some(_) => {}
            None => return Ok(duration_repr),
        }

        // parse the exponent of the input if present
        match self.current_byte {
            Some(byte) if byte.eq_ignore_ascii_case(&b'e') => {
                self.advance();
                let exponent = self.parse_exponent()?;
                duration_repr.exponent = exponent;
            }
            Some(_) => {}
            None => return Ok(duration_repr),
        }

        match self.current_byte {
            Some(_) if !self.time_units.is_empty() => {
                let unit = self.parse_time_unit()?;
                duration_repr.unit = unit;
            }
            Some(byte) => {
                return Err(ParseError::Syntax(
                    self.current_pos,
                    format!(
                        "No time units allowed but found: {}",
                        std::str::from_utf8(&[*byte]).unwrap_or("invalid utf8")
                    ),
                ))
            }
            None => return Ok(duration_repr),
        }

        // check we've reached the end of input
        match self.current_byte {
            Some(byte) => Err(ParseError::Syntax(
                self.current_pos,
                format!(
                    "Expected end of input but found: {}",
                    std::str::from_utf8(&[*byte]).unwrap_or("invalid utf8")
                ),
            )),
            None => Ok(duration_repr),
        }
    }

    fn parse_time_unit(&mut self) -> Result<TimeUnit, ParseError> {
        let mut max_bytes = self.time_units.max_length();
        let mut bytes = Vec::<u8>::with_capacity(max_bytes);
        while let Some(byte) = self.current_byte {
            if max_bytes != 0 {
                bytes.push(*byte);
                self.advance();
                max_bytes -= 1;
            } else {
                break;
            }
        }

        let string = std::str::from_utf8(bytes.as_slice()).map_err(|_| {
            ParseError::Syntax(self.current_pos - bytes.len(), "Invalid utf8".to_string())
        })?;
        // TODO: Remove the need to convert to utf8 and store the ids as bytes.
        self.time_units.get(string).ok_or(ParseError::Syntax(
            self.current_pos - bytes.len(),
            format!("Invalid time unit: {string}"),
        ))
    }

    fn parse_digits(
        &mut self,
        mut max: usize,
        strip_leading_zeroes: bool,
    ) -> Result<Vec<u8>, ParseError> {
        debug_assert!(
            self.current_byte.is_some(),
            "Call this function only when there is at lease one digit present"
        );
        // Using `size_hint()` is a rough (but always correct) estimation for an upper bound.
        // However, using maybe more memory than needed spares the costly memory reallocations and
        // maximum memory used is just around `1kB` per parsed number.
        let capacity = max.min(self.iterator.size_hint().1.unwrap() + 1);
        let mut digits = Vec::<u8>::with_capacity(capacity);

        while let Some(byte) = self.current_byte {
            let digit = byte.wrapping_sub(b'0');
            if digit < 10 {
                if strip_leading_zeroes && digits.is_empty() && digit == 0 {
                    // do nothing and just advance
                } else if max > 0 {
                    digits.push(digit);
                    max -= 1;
                }
                self.advance();
            } else {
                break;
            }
        }

        if strip_leading_zeroes && digits.is_empty() {
            digits.push(0);
        }

        Ok(digits)
    }

    fn parse_infinity(&mut self) -> Result<(), ParseError> {
        let expected = [b'i', b'n', b'f', b'i', b'n', b'i', b't', b'y'];
        for (pos, byte) in expected.iter().enumerate() {
            match self.current_byte {
                Some(current) if current.eq_ignore_ascii_case(byte) => self.advance(),
                Some(_) => {
                    return Err(ParseError::Syntax(
                        self.current_pos,
                        "Invalid infinity".to_string(),
                    ))
                } // wrong character
                None if pos == 3 => return Ok(()), // short `inf` is allowed
                None => {
                    return Err(ParseError::Syntax(
                        self.current_pos,
                        "Unexpected end of input".to_string(),
                    ))
                }
            }
        }

        // assure we've reached the end of input
        if self.current_byte.is_none() {
            Ok(())
        } else {
            Err(ParseError::Syntax(
                self.current_pos,
                "Expected end of input".to_string(),
            ))
        }
    }

    /// Parse and consume the sign if present. Return true if sign is negative.
    fn parse_sign_is_negative(&mut self) -> Result<bool, ParseError> {
        match self.current_byte {
            Some(byte) if *byte == b'+' => {
                self.advance();
                Ok(false)
            }
            Some(byte) if *byte == b'-' => {
                self.advance();
                Ok(true)
            }
            Some(_) => Ok(false),
            None => Err(ParseError::Syntax(
                self.current_pos,
                "Unexpected end of input".to_string(),
            )),
        }
    }

    fn parse_exponent(&mut self) -> Result<i16, ParseError> {
        let is_negative = self.parse_sign_is_negative()?;

        let mut exponent = 0i16;
        while let Some(byte) = self.current_byte {
            let digit = byte.wrapping_sub(b'0');
            if digit < 10 {
                exponent = exponent * 10 + digit as i16;
                if (is_negative && exponent <= 1022) || (!is_negative && exponent <= 1023) {
                    self.advance();
                } else {
                    return Err(ParseError::Overflow);
                }
            } else {
                break;
            }
        }

        Ok(if is_negative { -exponent } else { exponent })
    }
}

/// A builder with methods to configure the parser with a set of time units.
#[derive(Debug, Default)]
pub struct DurationParser<'a> {
    time_units: TimeUnits<'a>,
}

impl<'a> DurationParser<'a> {
    /// Construct the parser with default time units.
    pub fn new() -> Self {
        Self {
            time_units: TimeUnits::with_default_time_units(),
        }
    }

    /// Initialize the parser with a custom set of time units.
    pub fn with_time_units(time_units: &[TimeUnit]) -> Self {
        Self {
            time_units: TimeUnits::with_time_units(time_units),
        }
    }

    /// Return a parser without time units.
    ///
    /// This is the fastest parser.
    pub fn without_time_units() -> Self {
        Self {
            time_units: TimeUnits::new(),
        }
    }

    /// Construct a parser with all available time units.
    pub fn with_all_time_units() -> Self {
        Self {
            time_units: TimeUnits::with_all_time_units(),
        }
    }

    /// Add a time unit to the current set of time units.
    pub fn time_unit(&mut self, unit: TimeUnit) -> &mut Self {
        self.time_units.add_time_unit(unit);
        self
    }

    /// Add a list of time unit to the current set of time units.
    pub fn time_units(&mut self, units: &[TimeUnit]) -> &mut Self {
        self.time_units.add_time_units(units);
        self
    }

    /// Parse the `source` string into a duration.
    pub fn parse(&mut self, source: &str) -> Result<Duration, ParseError> {
        let mut parser = ReprParser::new(source, &self.time_units);
        parser.parse().and_then(|mut repr| repr.parse())
    }
}

/// Parse a string into a [`Duration`] by accepting a source string similar to floating point with
/// the default set of time units.
///
/// No whitespace is allowed in the source string. By parsing directly into a `u64` for the whole
/// number part (the [`Duration`] seconds) and `u32` for the fraction part (the [`Duration`] nano
/// seconds), we avoid the possibly lossy intermediate conversion to a `f64` and can represent the
/// exact user input as `Duration`. We can also represent valid durations, which
/// [`Duration::from_secs_f64`] can not parse without errors, like `format!("{}.0", u64::MAX)`. The
/// accepted grammar is (closely related to [`f64::from_str`]):
///
/// The parsed [`Duration`] saturates at `seconds == u64::MAX`, `nanos (max) == .999999999` and is
/// bounded below at `nanos (min if not 0) == .000000001`. Infinity values like `inf`, `+infinity`
/// etc. are valid input and resolve to `Duration::MAX`.
///
/// # Errors
///
/// This function will return an error when parsing fails, the `src` was negative (`-0.0` counts as
/// not negative) or the exponent wasn't in the allowed range (`-1022..=1023`).
///
/// # Examples
///
/// ```rust
/// use fundu::{parse_duration, ParseError};
/// use std::time::Duration;
///
/// let duration = parse_duration("+1.09e1").unwrap();
/// assert_eq!(duration, Duration::new(10, 900_000_000));
///
/// assert_eq!(parse_duration("Not a number"), Err(ParseError::Syntax(0, "Invalid character: N".to_string())));
/// ```
///
/// [`f64::from_str`]: https://doc.rust-lang.org/std/primitive.f64.html#method.from_str
pub fn parse_duration(string: &str) -> Result<Duration, ParseError> {
    DurationParser::new().parse(string)
}
