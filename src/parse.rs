// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! This module is the working horse of the parser. Public interfaces to the parser are located in
//! the main library `lib.rs`.

use crate::error::ParseError;
use crate::time::{TimeUnit, TimeUnits};
use std::cmp::Ordering;
use std::time::Duration;

const ATTO_MULTIPLIER: u64 = 1_000_000_000_000_000_000;
const ATTO_TO_NANO: u64 = 1_000_000_000;

/// An intermediate representation of seconds.
///
/// Optionally append `usize` amount of zeroes.
struct Seconds<'a>(Option<&'a [u8]>, Option<&'a [u8]>, Option<usize>);

impl<'a> Seconds<'a> {
    const ZERO: Self = Seconds(None, None, None);

    #[inline(always)]
    fn parse(&self) -> Result<u64, ParseError> {
        if self.is_zero() {
            return Ok(0);
        }

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

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.0.map_or(true, |v| v.is_empty()) && self.1.map_or(true, |v| v.is_empty())
    }
}

/// An intermediate representation of atto seconds.
///
/// Optionally prepend `usize` amount of zeroes.
struct Attos<'a>(Option<usize>, Option<&'a [u8]>, Option<&'a [u8]>);

impl<'a> Attos<'a> {
    const ZERO: Self = Attos(None, None, None);

    #[inline(always)]
    fn parse(&self) -> u64 {
        if self.is_zero() {
            return 0;
        }

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

    #[inline(always)]
    fn is_zero(&self) -> bool {
        self.1.map_or(true, |v| v.is_empty()) && self.2.map_or(true, |v| v.is_empty())
    }
}

#[derive(Debug, Default)]
pub struct DurationRepr {
    is_negative: bool,
    is_infinite: bool,
    whole: Option<Vec<u8>>,
    fract: Option<Vec<u8>>,
    exponent: i16,
    unit: TimeUnit,
}

impl DurationRepr {
    #[inline(always)]
    pub fn parse(&mut self) -> Result<Duration, ParseError> {
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
            Err(_) => unreachable!(), // cov:excl-line only ParseError::Overflow is returned by `Seconds::parse`
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

pub(crate) struct ReprParser<'a> {
    current_byte: Option<&'a u8>,
    current_pos: usize,
    time_units: &'a TimeUnits,
    input: &'a [u8],
}

/// Parse a source string into a [`DurationRepr`].
impl<'a> ReprParser<'a> {
    #[inline(always)]
    pub fn new(input: &'a str, time_units: &'a TimeUnits) -> Self {
        let input = input.as_bytes();
        Self {
            current_byte: input.first(),
            input,
            current_pos: 0,
            time_units,
        }
    }

    #[inline(always)]
    fn advance(&mut self) {
        self.current_pos += 1;
        self.current_byte = self.input.get(self.current_pos);
    }

    #[inline(always)]
    pub fn parse(&mut self) -> Result<DurationRepr, ParseError> {
        let mut duration_repr = DurationRepr {
            unit: self.time_units.default,
            ..Default::default()
        };

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
                    format!("Invalid character: '{}'", *byte as char),
                ));
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
                    Some(_) | None if duration_repr.whole.is_none() => {
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
                    format!("No time units allowed but found: '{}'", *byte as char),
                ));
            }
            None => return Ok(duration_repr),
        }

        // check we've reached the end of input
        match self.current_byte {
            Some(byte) => Err(ParseError::Syntax(
                self.current_pos,
                format!("Expected end of input but found: '{}'", *byte as char),
            )),
            None => Ok(duration_repr),
        }
    }

    #[inline(always)]
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

        // Safety: The input of `parse` is &str and therefore valid utf-8
        let string = unsafe { std::str::from_utf8_unchecked(bytes.as_slice()) };
        self.time_units.get(string).ok_or(ParseError::Syntax(
            self.current_pos - bytes.len(),
            format!("Invalid time unit: {string}"),
        ))
    }

    #[inline(always)]
    fn parse_digits(
        &mut self,
        mut max: usize,
        strip_leading_zeroes: bool,
    ) -> Result<Vec<u8>, ParseError> {
        // cov:excl-start
        debug_assert!(
            self.current_byte.is_some(),
            "Call this function only when there is at lease one digit present"
        ); // cov:excl-stop

        // Using `size_hint()` is a rough (but always correct) estimation for an upper bound.
        // However, using maybe more memory than needed spares the costly memory reallocations and
        // maximum memory used is just around `1kB` per parsed number.
        let capacity = max.min(self.input.len() - self.current_pos + 1);
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

    #[inline(always)]
    fn parse_infinity(&mut self) -> Result<(), ParseError> {
        let expected = [b'i', b'n', b'f', b'i', b'n', b'i', b't', b'y'];
        for (pos, byte) in expected.iter().enumerate() {
            match self.current_byte {
                Some(current) if current.eq_ignore_ascii_case(byte) => self.advance(),
                // wrong character
                Some(_) => {
                    return Err(ParseError::Syntax(
                        self.current_pos,
                        "Invalid infinity".to_string(),
                    ))
                }
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
    #[inline(always)]
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

    #[inline(always)]
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
