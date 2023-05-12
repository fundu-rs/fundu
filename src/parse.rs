// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! This module is the working horse of the parser. Public interfaces to the parser are located in
//! the main library `lib.rs`.

use std::cmp::Ordering::{Equal, Greater, Less};
use std::ops::Neg;
use std::str::Utf8Error;
use std::time::Duration as StdDuration;

use crate::config::{Config, Delimiter, DEFAULT_CONFIG};
use crate::error::ParseError;
use crate::time::{Duration, Multiplier, TimeUnit, TimeUnitsLike};
use crate::util::POW10;

const ATTOS_PER_SEC: u64 = 1_000_000_000_000_000_000;
const ATTOS_PER_NANO: u64 = 1_000_000_000;

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Parser<'a> {
    pub(crate) config: Config<'a>,
}

impl<'a> Parser<'a> {
    pub(crate) const fn new() -> Self {
        Self {
            config: DEFAULT_CONFIG,
        }
    }

    pub(crate) const fn with_config(config: Config<'a>) -> Self {
        Self { config }
    }

    fn parse_multiple(
        &self,
        source: &str,
        delimiter: Delimiter,
        conjunctions: &[&str],
        time_units: &dyn TimeUnitsLike,
        keywords: Option<&dyn TimeUnitsLike>,
    ) -> Result<Duration, ParseError> {
        let mut duration = Duration::ZERO;

        let mut parser = &mut ReprParserMultiple::new(source, delimiter, conjunctions);
        loop {
            let (mut duration_repr, maybe_parser) =
                parser.parse(&self.config, time_units, keywords)?;
            let parsed_duration = duration_repr.parse()?;
            duration = if !self.config.allow_negative && parsed_duration.is_negative() {
                return Err(ParseError::NegativeNumber);
            } else if parsed_duration.is_zero() {
                duration
            } else if duration.is_zero() {
                parsed_duration
            } else {
                duration.saturating_add(parsed_duration)
            };
            match maybe_parser {
                Some(p) => parser = p,
                None => break Ok(duration),
            }
        }
    }

    fn parse_single(
        &self,
        source: &str,
        time_units: &dyn TimeUnitsLike,
        keywords: Option<&dyn TimeUnitsLike>,
    ) -> Result<Duration, ParseError> {
        ReprParserSingle::new(source)
            .parse(&self.config, time_units, keywords)
            .and_then(|mut duration_repr| {
                duration_repr.parse().and_then(|duration| {
                    if !self.config.allow_negative && duration.is_negative() {
                        Err(ParseError::NegativeNumber)
                    } else {
                        Ok(duration)
                    }
                })
            })
    }

    /// Parse the `source` string into a saturating [`crate::time::Duration`]
    #[inline]
    pub(crate) fn parse(
        &self,
        source: &str,
        time_units: &dyn TimeUnitsLike,
        keywords: Option<&dyn TimeUnitsLike>,
    ) -> Result<Duration, ParseError> {
        if let Some(delimiter) = self.config.parse_multiple_delimiter {
            self.parse_multiple(
                source,
                delimiter,
                self.config.parse_multiple_conjunctions.unwrap_or_default(),
                time_units,
                keywords,
            )
        } else {
            self.parse_single(source, time_units, keywords)
        }
    }
}

trait Parse8Digits {
    // This method is based on the work of Johnny Lee and his blog post
    // https://johnnylee-sde.github.io/Fast-numeric-string-to-int
    unsafe fn parse_8_digits(digits: &[u8]) -> u64 {
        // cov:excl-start
        debug_assert!(
            digits.len() >= 8,
            "Call this method only if digits has length >= 8"
        ); // cov:excl-stop

        let ptr = digits.as_ptr() as *const u64;
        let mut num = u64::from_le(ptr.read_unaligned());
        num = ((num & 0x0F0F0F0F0F0F0F0F).wrapping_mul(2561)) >> 8;
        num = ((num & 0x00FF00FF00FF00FF).wrapping_mul(6553601)) >> 16;
        num = ((num & 0x0000FFFF0000FFFF).wrapping_mul(42949672960001)) >> 32;
        num
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
struct Whole(usize, usize);

impl Parse8Digits for Whole {}

impl Whole {
    #[inline]
    fn parse_slice(mut seconds: u64, digits: &[u8]) -> Result<u64, ParseError> {
        if digits.len() >= 8 {
            let mut iter = digits.chunks_exact(8);
            for digits in iter.by_ref() {
                // SAFETY: We have chunks of exactly 8 bytes
                match seconds
                    .checked_mul(100_000_000)
                    .and_then(|s| s.checked_add(unsafe { Self::parse_8_digits(digits) }))
                {
                    Some(s) => seconds = s,
                    None => {
                        return Err(ParseError::Overflow);
                    }
                }
            }
            for num in iter.remainder() {
                match seconds
                    .checked_mul(10)
                    .and_then(|s| s.checked_add((*num - b'0') as u64))
                {
                    Some(s) => seconds = s,
                    None => {
                        return Err(ParseError::Overflow);
                    }
                }
            }
        } else {
            for num in digits {
                match seconds
                    .checked_mul(10)
                    .and_then(|s| s.checked_add((*num - b'0') as u64))
                {
                    Some(s) => seconds = s,
                    None => {
                        return Err(ParseError::Overflow);
                    }
                }
            }
        }
        Ok(seconds)
    }

    fn parse(
        &self,
        digits: &[u8],
        append: Option<&[u8]>,
        zeros: Option<usize>,
    ) -> Result<u64, ParseError> {
        if digits.is_empty() && append.is_none() {
            return Ok(0);
        }

        let seconds = Self::parse_slice(0, digits).and_then(|s| match append {
            Some(append) => Self::parse_slice(s, append),
            None => Ok(s),
        })?;
        if seconds == 0 {
            Ok(0)
        } else {
            match zeros {
                Some(num_zeros) if num_zeros > 0 => match POW10.get(num_zeros) {
                    Some(pow) => Ok(seconds.saturating_mul(*pow)),
                    None => Err(ParseError::Overflow),
                },
                Some(_) | None => Ok(seconds),
            }
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.1 - self.0
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
struct Fract(usize, usize);

impl Parse8Digits for Fract {}

impl Fract {
    #[inline]
    fn parse_slice(mut multi: u64, num_skip: usize, digits: &[u8]) -> (u64, u64) {
        let mut attos = 0;
        let len = digits.len();

        if multi >= 100_000_000 && len >= 8 {
            let max = 18usize.saturating_sub(num_skip);
            let mut iter = digits
                .get(0..if len > max { max } else { len })
                .unwrap()
                .chunks_exact(8);
            for digits in iter.by_ref() {
                multi /= 100_000_000;
                // SAFETY: The length of digits is exactly 8
                attos += unsafe { Self::parse_8_digits(digits) } * multi;
            }
            for num in iter.remainder() {
                multi /= 10;
                attos += (*num - b'0') as u64 * multi;
            }
        } else if multi > 0 && len > 0 {
            for num in digits {
                multi /= 10;
                if multi == 0 {
                    return (0, attos);
                }
                attos += (*num - b'0') as u64 * multi;
            }
            // else would be reached if multi or len are zero but these states are already handled
            // in parse
        } // cov:excl-line
        (multi, attos)
    }

    fn parse(&self, digits: &[u8], prepend: Option<&[u8]>, zeros: Option<usize>) -> u64 {
        if digits.is_empty() && prepend.is_none() {
            return 0;
        }

        let num_zeros = zeros.unwrap_or_default();
        let pow = match POW10.get(num_zeros) {
            Some(pow) => pow,
            None => return 0,
        };
        let multi = ATTOS_PER_SEC / pow;
        if multi == 0 {
            return 0;
        }

        match prepend {
            Some(prepend) if num_zeros + prepend.len() >= 18 => {
                let (_, attos) = Self::parse_slice(multi, num_zeros, prepend);
                attos
            }
            Some(prepend) if !prepend.is_empty() => {
                let (multi, attos) = Self::parse_slice(multi, num_zeros, prepend);
                let (_, remainder) = Self::parse_slice(multi, num_zeros + prepend.len(), digits);
                attos + remainder
            }
            Some(_) | None => {
                let (_, attos) = Self::parse_slice(multi, num_zeros, digits);
                attos
            }
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.1 - self.0
    }
}

#[derive(Debug, Default)]
pub(crate) struct DurationRepr<'input> {
    unit: TimeUnit,
    number_is_optional: bool,
    is_negative: bool,
    is_infinite: bool,
    whole: Option<Whole>,
    fract: Option<Fract>,
    input: &'input [u8],
    exponent: i16,
    multiplier: Multiplier,
}

impl<'input> DurationRepr<'input> {
    pub(crate) fn parse(&mut self) -> Result<Duration, ParseError> {
        if self.is_infinite {
            return Ok(Duration::from_std(self.is_negative, StdDuration::MAX));
        }

        let (digits, whole, fract) = match (self.whole.take(), self.fract.take()) {
            (None, None) if self.number_is_optional => {
                let digits = Some(vec![0x31]);
                (digits, Whole(0, 1), Fract(1, 1))
            }
            (None, None) => unreachable!(), // cov:excl-line
            (None, Some(fract)) => (None, Whole(fract.0, fract.0), fract),
            (Some(whole), None) => {
                let fract_start_and_end = whole.1;
                (None, whole, Fract(fract_start_and_end, fract_start_and_end))
            }
            (Some(whole), Some(fract)) => (None, whole, fract),
        };

        let digits = digits.as_ref().map_or(self.input, |d| d.as_slice());

        // Panic on overflow during the multiplication of the multipliers or adding the exponents
        let Multiplier(coefficient, exponent) = self.unit.multiplier() * self.multiplier;
        let exponent = exponent as i32 + self.exponent as i32;

        // The maximum absolute value of the exponent is `2 * abs(i16::MIN)`, so it is safe to cast
        // to usize
        let exponent_abs: usize = exponent.unsigned_abs().try_into().unwrap();

        // We're operating on slices to minimize runtime costs. Applying the exponent before parsing
        // to integers is necessary, since the exponent can move digits into the to be considered
        // final integer domain.
        let (seconds, attos) = match exponent.cmp(&0) {
            Less if whole.len() > exponent_abs => {
                let seconds = whole.parse(&digits[whole.0..whole.1 - exponent_abs], None, None);
                let attos = if seconds.is_ok() {
                    Some(fract.parse(
                        &digits[fract.0..fract.1],
                        Some(&digits[whole.1 - exponent_abs..whole.1]),
                        None,
                    ))
                } else {
                    None
                };
                (Some(seconds), attos)
            }
            Less => {
                let attos = Some(fract.parse(
                    &digits[fract.0..fract.1],
                    Some(&digits[whole.0..whole.1]),
                    Some(exponent_abs - whole.len()),
                ));
                (None, attos)
            }
            Equal => {
                let seconds = whole.parse(&digits[whole.0..whole.1], None, None);
                let attos = if seconds.is_ok() {
                    Some(fract.parse(&digits[fract.0..fract.1], None, None))
                } else {
                    None
                };
                (Some(seconds), attos)
            }
            Greater if fract.len() > exponent_abs => {
                let seconds = whole.parse(
                    &digits[whole.0..whole.1],
                    Some(&digits[fract.0..fract.0 + exponent_abs]),
                    None,
                );
                let attos = if seconds.is_ok() {
                    Some(fract.parse(&digits[fract.0 + exponent_abs..fract.1], None, None))
                } else {
                    None
                };
                (Some(seconds), attos)
            }
            Greater => {
                let seconds = whole.parse(
                    &digits[whole.0..whole.1],
                    Some(&digits[fract.0..fract.1]),
                    Some(exponent_abs - fract.len()),
                );
                (Some(seconds), None)
            }
        };

        let duration_is_negative = self.is_negative ^ coefficient.is_negative();

        // Finally, parse the seconds and atto seconds and interpret a seconds overflow as
        // maximum `Duration`.
        let (seconds, attos) = match seconds {
            Some(result) => match result {
                Ok(seconds) => (seconds, attos.unwrap_or_default()),
                Err(ParseError::Overflow) if duration_is_negative => {
                    return Ok(Duration::MIN);
                }
                Err(ParseError::Overflow) => {
                    return Ok(Duration::MAX);
                }
                // only ParseError::Overflow is returned by `Seconds::parse`
                Err(_) => unreachable!(), // cov:excl-line
            },
            None => (0, attos.unwrap_or_default()),
        };

        // allow -0 or -0.0 etc., or in general numbers x with abs(x) < 1e-18 and interpret them
        // as zero duration
        if seconds == 0 && attos == 0 {
            Ok(Duration::ZERO)
        } else if coefficient == 1 || coefficient == -1 {
            Ok(Duration::from_std(
                duration_is_negative,
                StdDuration::new(seconds, (attos / ATTOS_PER_NANO) as u32),
            ))
        } else {
            let unsigned_coefficient = coefficient.unsigned_abs();

            let attos = attos as u128 * (unsigned_coefficient as u128);
            Ok(
                match seconds
                    .checked_mul(unsigned_coefficient)
                    .and_then(|s| s.checked_add((attos / (ATTOS_PER_SEC as u128)) as u64))
                {
                    Some(s) => Duration::from_std(
                        duration_is_negative,
                        StdDuration::new(
                            s,
                            ((attos / (ATTOS_PER_NANO as u128)) % 1_000_000_000) as u32,
                        ),
                    ),
                    None if duration_is_negative => Duration::MIN,
                    None => Duration::MAX,
                },
            )
        }
    }
}

struct BytesRange(usize, usize);

struct Bytes<'a> {
    current_pos: usize, // keep first. Has better performance.
    current_byte: Option<&'a u8>,
    input: &'a [u8],
}

impl<'a> Bytes<'a> {
    #[inline]
    fn new(input: &'a [u8]) -> Self {
        Self {
            current_pos: 0,
            current_byte: input.first(),
            input,
        }
    }

    #[inline]
    fn advance(&mut self) {
        self.current_pos += 1;
        self.current_byte = self.input.get(self.current_pos);
    }

    #[inline]
    unsafe fn advance_by(&mut self, num: usize) {
        self.current_pos += num;
        self.current_byte = self.input.get(self.current_pos);
    }

    fn advance_to<F>(&mut self, delimiter: F) -> &'a [u8]
    where
        F: Fn(u8) -> bool,
    {
        let start = self.current_pos;
        while let Some(byte) = self.current_byte {
            if delimiter(*byte) {
                break;
            } else {
                self.advance()
            }
        }
        &self.input[start..self.current_pos]
    }

    #[inline]
    fn peek(&self, num: usize) -> Option<&[u8]> {
        self.input.get(self.current_pos..self.current_pos + num)
    }

    #[inline]
    fn get_remainder(&self) -> &[u8] {
        &self.input[self.current_pos..]
    }

    #[inline]
    unsafe fn get_remainder_str_unchecked(&self) -> &str {
        std::str::from_utf8_unchecked(self.get_remainder())
    }

    #[inline]
    fn get_current_str(&self, start: usize) -> Result<&str, Utf8Error> {
        std::str::from_utf8(&self.input[start..self.current_pos])
    }

    #[inline]
    fn finish(&mut self) {
        self.current_pos = self.input.len();
        self.current_byte = None
    }

    #[inline]
    fn reset(&mut self, position: usize) {
        self.current_pos = position;
        self.current_byte = self.input.get(position);
    }

    #[inline]
    fn parse_digit(&mut self) -> Option<u8> {
        self.current_byte.and_then(|byte| {
            let digit = byte.wrapping_sub(b'0');
            if digit < 10 {
                self.advance();
                Some(*byte)
            } else {
                None
            }
        })
    }

    fn parse_digits_strip_zeros(&mut self) -> BytesRange {
        debug_assert!(
            self.current_byte
                .map_or(false, |byte| byte.is_ascii_digit())
        ); // cov:excl-stop
        const ASCII_EIGHT_ZEROS: u64 = 0x3030303030303030;

        let mut start = self.current_pos;
        let mut strip_leading_zeros = true;
        while let Some(eight) = self.parse_8_digits() {
            if strip_leading_zeros {
                if eight == ASCII_EIGHT_ZEROS {
                    start += 8;
                } else {
                    strip_leading_zeros = false;

                    // eight is little endian so we need to count the trailing zeros
                    let leading_zeros = (eight - ASCII_EIGHT_ZEROS).trailing_zeros() / 8;
                    start += leading_zeros as usize;
                }
            }
        }

        while let Some(byte) = self.current_byte {
            let digit = byte.wrapping_sub(b'0');
            if digit < 10 {
                if strip_leading_zeros {
                    if digit == 0 {
                        start += 1;
                    } else {
                        strip_leading_zeros = false;
                    }
                }
                self.advance();
            } else {
                break;
            }
        }

        BytesRange(start, self.current_pos)
    }

    fn parse_digits(&mut self) -> BytesRange {
        debug_assert!(
            self.current_byte
                .map_or(false, |byte| byte.is_ascii_digit())
        ); // cov:excl-stop

        let start = self.current_pos;
        while self.parse_8_digits().is_some() {}
        while self.parse_digit().is_some() {}

        BytesRange(start, self.current_pos)
    }

    /// This method is based on the work of Daniel Lemire and his blog post
    /// <https://lemire.me/blog/2018/09/30/quickly-identifying-a-sequence-of-digits-in-a-string-of-characters/>
    fn parse_8_digits(&mut self) -> Option<u64> {
        self.input
            .get(self.current_pos..(self.current_pos + 8))
            .and_then(|digits| {
                let ptr = digits.as_ptr() as *const u64;
                // SAFETY: We just ensured there are 8 bytes
                let num = u64::from_le(unsafe { ptr.read_unaligned() });
                if (num & (num.wrapping_add(0x0606060606060606)) & 0xf0f0f0f0f0f0f0f0)
                    == 0x3030303030303030
                {
                    unsafe { self.advance_by(8) }
                    Some(num)
                } else {
                    None
                }
            })
    }

    #[inline]
    fn next_is_ignore_ascii_case(&self, word: &[u8]) -> bool {
        self.peek(word.len())
            .map_or(false, |bytes| bytes.eq_ignore_ascii_case(word))
    }

    #[inline]
    fn is_end_of_input(&self) -> bool {
        self.current_byte.is_none()
    }

    #[inline]
    fn check_end_of_input(&self) -> Result<(), ParseError> {
        match self.current_byte {
            Some(byte) => Err(ParseError::Syntax(
                self.current_pos,
                format!("Expected end of input but found: '{}'", *byte as char),
            )),
            None => Ok(()),
        }
    }

    fn try_consume_delimiter(&mut self, delimiter: Delimiter) -> Result<(), ParseError> {
        debug_assert!(delimiter(*self.current_byte.unwrap())); // cov:excl-line

        let start = self.current_pos;
        self.advance();
        while let Some(byte) = self.current_byte {
            if delimiter(*byte) {
                self.advance()
            } else {
                break;
            }
        }

        match self.current_byte {
            Some(_) => Ok(()),
            None => Err(ParseError::Syntax(
                start,
                "Input may not end with a delimiter".to_string(),
            )),
        }
    }
}

trait ReprParserTemplate<'a> {
    type Output;

    fn bytes(&mut self) -> &mut Bytes<'a>;

    fn make_output(&'a mut self, duration_repr: DurationRepr<'a>) -> Self::Output;

    fn parse_infinity_remainder(
        &'a mut self,
        duration_repr: DurationRepr<'a>,
    ) -> Result<Self::Output, ParseError>;

    fn parse_keyword(
        &mut self,
        keywords: Option<&dyn TimeUnitsLike>,
    ) -> Result<Option<(TimeUnit, Multiplier)>, ParseError>;

    fn parse_time_unit(
        &mut self,
        config: &Config,
        time_units: &dyn TimeUnitsLike,
    ) -> Result<Option<(TimeUnit, Multiplier)>, ParseError>;

    fn parse_number_time_unit(
        &mut self,
        duration_repr: &mut DurationRepr<'a>,
        config: &Config,
        time_units: &dyn TimeUnitsLike,
    ) -> Result<bool, ParseError>;

    fn finalize(&'a mut self, duration_repr: DurationRepr<'a>) -> Result<Self::Output, ParseError>;

    #[inline]
    fn parse_whole(&mut self) -> Whole {
        let BytesRange(start, end) = self.bytes().parse_digits_strip_zeros();
        Whole(start, end)
    }

    fn parse(
        &'a mut self,
        config: &Config,
        time_units: &dyn TimeUnitsLike,
        keywords: Option<&dyn TimeUnitsLike>,
    ) -> Result<Self::Output, ParseError> {
        if self.bytes().current_byte.is_none() {
            return Err(ParseError::Empty);
        }

        let mut duration_repr = DurationRepr {
            unit: config.default_unit,
            input: self.bytes().input,
            number_is_optional: config.number_is_optional,
            ..Default::default()
        };

        self.parse_number_sign(&mut duration_repr)?;

        // parse infinity, keywords or the whole number part of the input
        match self.bytes().current_byte.cloned() {
            Some(byte) if byte.is_ascii_digit() => {
                duration_repr.whole = Some(self.parse_whole());
            }
            Some(byte) if byte == b'.' => {}
            Some(_)
                if !config.disable_infinity && self.bytes().next_is_ignore_ascii_case(b"inf") =>
            {
                // SAFETY: We just checked that there are at least 3 bytes
                unsafe { self.bytes().advance_by(3) }
                return self.parse_infinity_remainder(duration_repr);
            }
            Some(_) if keywords.is_some() => {
                if let Some((unit, multi)) = self.parse_keyword(keywords)? {
                    duration_repr.number_is_optional = true;
                    duration_repr.unit = unit;
                    duration_repr.multiplier = multi;
                    return Ok(self.make_output(duration_repr));
                } else if config.number_is_optional {
                    // do nothing
                } else {
                    // SAFETY: The input str is utf-8 and we have only parsed valid utf-8 so far
                    return Err(ParseError::Syntax(
                        self.bytes().current_pos,
                        format!("Invalid input: '{}'", unsafe {
                            self.bytes().get_remainder_str_unchecked()
                        }),
                    ));
                }
            }
            Some(_) if config.number_is_optional => {}
            Some(_) => {
                // SAFETY: The input str is utf-8 and we have only parsed ascii characters so far
                return Err(ParseError::Syntax(
                    self.bytes().current_pos,
                    format!("Invalid input: '{}'", unsafe {
                        self.bytes().get_remainder_str_unchecked()
                    }),
                ));
            }
            None => {
                return Err(ParseError::Syntax(
                    self.bytes().current_pos,
                    "Unexpected end of input".to_string(),
                ));
            }
        }

        if !self.parse_number_fraction(&mut duration_repr, config.disable_fraction)? {
            return Ok(self.make_output(duration_repr));
        }

        if !self.parse_number_exponent(&mut duration_repr, config.disable_exponent)? {
            return Ok(self.make_output(duration_repr));
        }

        if !self.parse_number_delimiter(config.allow_delimiter)? {
            return Ok(self.make_output(duration_repr));
        }

        if !self.parse_number_time_unit(&mut duration_repr, config, time_units)? {
            return Ok(self.make_output(duration_repr));
        }

        self.finalize(duration_repr)
    }

    /// Parse and consume the sign if present. Return true if sign is negative.
    fn parse_sign_is_negative(&mut self) -> Result<bool, ParseError> {
        let bytes = self.bytes();
        match bytes.current_byte {
            Some(byte) if *byte == b'+' => {
                bytes.advance();
                Ok(false)
            }
            Some(byte) if *byte == b'-' => {
                bytes.advance();
                Ok(true)
            }
            Some(_) => Ok(false),
            None => Err(ParseError::Syntax(
                bytes.current_pos,
                "Unexpected end of input".to_string(),
            )),
        }
    }

    fn parse_number_sign(&mut self, duration_repr: &mut DurationRepr) -> Result<(), ParseError> {
        if self.parse_sign_is_negative()? {
            duration_repr.is_negative = true;
        }
        Ok(())
    }

    #[inline]
    fn parse_fract(&mut self) -> Fract {
        let BytesRange(start, end) = self.bytes().parse_digits();
        Fract(start, end)
    }

    fn parse_number_fraction(
        &mut self,
        duration_repr: &mut DurationRepr<'a>,
        disable_fraction: bool,
    ) -> Result<bool, ParseError> {
        let bytes = self.bytes();
        match bytes.current_byte {
            Some(byte) if *byte == b'.' && !disable_fraction => {
                bytes.advance();
                let fract = match bytes.current_byte {
                    Some(byte) if byte.is_ascii_digit() => Some(self.parse_fract()),
                    Some(_) | None if duration_repr.whole.is_none() => {
                        // Use the decimal point as anchor for the error position. Subtraction by 1
                        // is safe since we were advancing by one before.
                        return Err(ParseError::Syntax(
                            bytes.current_pos - 1,
                            "Either the whole number part or the fraction must be present"
                                .to_string(),
                        ));
                    }
                    Some(_) => None,
                    None => return Ok(false),
                };
                duration_repr.fract = fract;
                Ok(true)
            }
            Some(byte) if *byte == b'.' => Err(ParseError::Syntax(
                bytes.current_pos,
                "No fraction allowed".to_string(),
            )),
            Some(_) => Ok(true),
            None => Ok(false),
        }
    }

    fn parse_exponent(&mut self) -> Result<i16, ParseError> {
        let is_negative = self.parse_sign_is_negative()?;
        let bytes = self.bytes();
        bytes.current_byte.ok_or_else(|| {
            ParseError::Syntax(
                bytes.current_pos,
                "Expected exponent but reached end of input".to_string(),
            )
        })?;

        let mut exponent = 0i16;
        while let Some(byte) = bytes.current_byte {
            let digit = byte.wrapping_sub(b'0');
            if digit < 10 {
                exponent = if is_negative {
                    match exponent
                        .checked_mul(10)
                        .and_then(|e| e.checked_sub(digit as i16))
                    {
                        Some(exponent) => exponent,
                        None => return Err(ParseError::NegativeExponentOverflow),
                    }
                } else {
                    match exponent
                        .checked_mul(10)
                        .and_then(|e| e.checked_add(digit as i16))
                    {
                        Some(exponent) => exponent,
                        None => return Err(ParseError::PositiveExponentOverflow),
                    }
                };
                bytes.advance();
            } else {
                break;
            }
        }

        Ok(exponent)
    }

    fn parse_number_exponent(
        &mut self,
        duration_repr: &mut DurationRepr<'a>,
        disable_exponent: bool,
    ) -> Result<bool, ParseError> {
        let bytes = self.bytes();
        match bytes.current_byte {
            Some(byte) if byte.eq_ignore_ascii_case(&b'e') && !disable_exponent => {
                bytes.advance();
                duration_repr.exponent = self.parse_exponent()?;
                Ok(true)
            }
            Some(byte) if byte.eq_ignore_ascii_case(&b'e') => Err(ParseError::Syntax(
                bytes.current_pos,
                "No exponent allowed".to_string(),
            )),
            Some(_) => Ok(true),
            None => Ok(false),
        }
    }

    fn parse_number_delimiter(&mut self, delimiter: Option<Delimiter>) -> Result<bool, ParseError> {
        let bytes = self.bytes();

        // If allow_delimiter is Some and there are any delimiters between the number and the time
        // unit, the delimiters are consumed before trying to parse the time units
        match (bytes.current_byte, delimiter) {
            (Some(byte), Some(delimiter)) if delimiter(*byte) => {
                bytes.try_consume_delimiter(delimiter)?;
                Ok(true)
            }
            (Some(_), _) => Ok(true),
            (None, _) => Ok(false),
        }
    }
}

pub(crate) struct ReprParserSingle<'a> {
    bytes: Bytes<'a>,
}

impl<'a> ReprParserSingle<'a> {
    fn new(input: &'a str) -> Self {
        Self {
            bytes: Bytes::new(input.as_bytes()),
        }
    }
}

impl<'a> ReprParserTemplate<'a> for ReprParserSingle<'a> {
    type Output = DurationRepr<'a>;

    #[inline]
    fn bytes(&mut self) -> &mut Bytes<'a> {
        &mut self.bytes
    }

    #[inline]
    fn make_output(&'a mut self, duration_repr: DurationRepr<'a>) -> Self::Output {
        duration_repr
    }

    #[inline]
    fn parse_infinity_remainder(
        &'a mut self,
        mut duration_repr: DurationRepr<'a>,
    ) -> Result<DurationRepr<'a>, ParseError> {
        if self.bytes.is_end_of_input() {
            duration_repr.is_infinite = true;
            return Ok(duration_repr);
        }

        let expected = b"inity";
        for byte in expected.iter() {
            match self.bytes.current_byte {
                Some(current) if current.eq_ignore_ascii_case(byte) => self.bytes.advance(),
                // wrong character
                Some(current) => {
                    return Err(ParseError::Syntax(
                        self.bytes.current_pos,
                        format!(
                            "Error parsing infinity: Invalid character '{}'",
                            *current as char
                        ),
                    ));
                }
                None => {
                    return Err(ParseError::Syntax(
                        self.bytes.current_pos,
                        "Error parsing infinity: Premature end of input".to_string(),
                    ));
                }
            }
        }

        duration_repr.is_infinite = true;
        self.bytes.check_end_of_input().map(|_| duration_repr)
    }

    #[inline]
    fn parse_keyword(
        &mut self,
        keywords: Option<&dyn TimeUnitsLike>,
    ) -> Result<Option<(TimeUnit, Multiplier)>, ParseError> {
        debug_assert!(keywords.is_some()); // cov:excl-line

        // SAFETY: we've only parsed valid utf-8 up to this point
        let keyword = unsafe { self.bytes.get_remainder_str_unchecked() };
        match keywords.unwrap().get(keyword) {
            None => Ok(None),
            some_time_unit => {
                self.bytes.finish();
                Ok(some_time_unit)
            }
        }
    }

    #[inline]
    fn parse_time_unit(
        &mut self,
        config: &Config,
        time_units: &dyn TimeUnitsLike,
    ) -> Result<Option<(TimeUnit, Multiplier)>, ParseError> {
        // cov:excl-start
        debug_assert!(
            self.bytes.current_byte.is_some(),
            "Don't call this function without being sure there's at least 1 byte remaining"
        ); // cov:excl-stop

        match config.allow_ago {
            Some(delimiter) => {
                let start = self.bytes.current_pos;
                let string =
                    std::str::from_utf8(self.bytes.advance_to(delimiter)).map_err(|error| {
                        ParseError::TimeUnit(
                            start + error.valid_up_to(),
                            "Invalid utf-8 when applying the delimiter".to_string(),
                        )
                    })?;

                // TODO: maybe change that to improve error message when `ago` is found without time
                // unit
                let (time_unit, mut multiplier) = if string.is_empty() {
                    return Ok(None);
                } else {
                    match time_units.get(string) {
                        None => {
                            return Err(ParseError::TimeUnit(
                                start,
                                format!("Invalid time unit: '{string}'"),
                            ));
                        }
                        Some(unit) => unit,
                    }
                };

                match self.bytes.current_byte {
                    Some(byte) if delimiter(*byte) => {
                        self.bytes.try_consume_delimiter(delimiter)?;
                        if self.bytes.next_is_ignore_ascii_case(b"ago") {
                            // SAFETY: We have checked that there are at least 3 bytes
                            unsafe { self.bytes.advance_by(3) };
                        }
                        multiplier = multiplier.neg();
                    }
                    Some(_) | None => {}
                };

                Ok(Some((time_unit, multiplier)))
            }
            None => {
                // SAFETY: The input of `parse` is &str and therefore valid utf-8 and we have read
                // only ascii characters up to this point.
                let string = unsafe { self.bytes.get_remainder_str_unchecked() };
                let result = match time_units.get(string) {
                    None => Err(ParseError::TimeUnit(
                        self.bytes.current_pos,
                        format!("Invalid time unit: '{string}'"),
                    )),
                    some_time_unit => Ok(some_time_unit),
                };
                self.bytes.finish();
                result
            }
        }
    }

    #[inline]
    fn parse_number_time_unit(
        &mut self,
        duration_repr: &mut DurationRepr<'a>,
        config: &Config,
        time_units: &dyn TimeUnitsLike,
    ) -> Result<bool, ParseError> {
        match self.bytes().current_byte.cloned() {
            Some(_) if !time_units.is_empty() => {
                if let Some((unit, multi)) = self.parse_time_unit(config, time_units)? {
                    duration_repr.unit = unit;
                    duration_repr.multiplier = multi;
                }
                Ok(true)
            }
            Some(_) => {
                // SAFETY: We've parsed only valid utf-8 so far
                Err(ParseError::TimeUnit(
                    self.bytes.current_pos,
                    format!("No time units allowed but found: '{}'", unsafe {
                        self.bytes.get_remainder_str_unchecked()
                    }),
                ))
            }
            None => Ok(false),
        }
    }

    #[inline]
    fn finalize(&'a mut self, duration_repr: DurationRepr<'a>) -> Result<Self::Output, ParseError> {
        self.bytes.check_end_of_input().map(|_| duration_repr)
    }
}

pub(crate) struct ReprParserMultiple<'a> {
    bytes: Bytes<'a>,
    delimiter: Delimiter,
    conjunctions: &'a [&'a str],
}

impl<'a> ReprParserMultiple<'a> {
    fn new(input: &'a str, delimiter: Delimiter, conjunctions: &'a [&'a str]) -> Self {
        Self {
            bytes: Bytes::new(input.as_bytes()),
            delimiter,
            conjunctions,
        }
    }

    fn try_consume_connection(&mut self) -> Result<(), ParseError> {
        let delimiter = self.delimiter;
        self.bytes.try_consume_delimiter(delimiter)?;
        let start = self.bytes.current_pos;
        if self.bytes.current_byte.is_some() {
            for word in self.conjunctions {
                if self.bytes.next_is_ignore_ascii_case(word.as_bytes()) {
                    // SAFETY: We're advancing by the amount of bytes of the word we just found
                    unsafe { self.bytes.advance_by(word.len()) };
                    match self.bytes.current_byte {
                        Some(byte) if delimiter(*byte) => {
                            self.bytes.try_consume_delimiter(delimiter)?
                        }
                        Some(byte) if byte.is_ascii_digit() => {}
                        Some(byte) => {
                            return Err(ParseError::Syntax(
                                self.bytes.current_pos,
                                format!(
                                    "A conjunction must be separated by a delimiter or digit but \
                                     found: '{}'",
                                    *byte as char
                                ),
                            ));
                        }
                        None => {
                            return Err(ParseError::Syntax(
                                start,
                                format!("Input may not end with a conjunction but found: '{word}'"),
                            ));
                        }
                    }
                    break;
                }
            }
        };
        Ok(())
    }
}

impl<'a> ReprParserTemplate<'a> for ReprParserMultiple<'a> {
    type Output = (DurationRepr<'a>, Option<&'a mut ReprParserMultiple<'a>>);

    #[inline]
    fn bytes(&mut self) -> &mut Bytes<'a> {
        &mut self.bytes
    }

    #[inline]
    fn make_output(&'a mut self, duration_repr: DurationRepr<'a>) -> Self::Output {
        (duration_repr, self.bytes().current_byte.map(|_| self))
    }

    #[inline]
    fn parse_infinity_remainder(
        &'a mut self,
        mut duration_repr: DurationRepr<'a>,
    ) -> Result<(DurationRepr<'a>, Option<&'a mut ReprParserMultiple<'a>>), ParseError> {
        let delimiter = self.delimiter;

        match self.bytes.current_byte {
            Some(byte) if delimiter(*byte) => {
                duration_repr.is_infinite = true;
                return self
                    .try_consume_connection()
                    .map(|_| (duration_repr, Some(self)));
            }
            Some(_) => {}
            None => {
                duration_repr.is_infinite = true;
                return Ok((duration_repr, None));
            }
        }

        let expected = b"inity";
        for byte in expected.iter() {
            match self.bytes.current_byte {
                Some(current) if current.eq_ignore_ascii_case(byte) => self.bytes.advance(),
                // wrong character
                Some(current) => {
                    return Err(ParseError::Syntax(
                        self.bytes.current_pos,
                        format!(
                            "Error parsing infinity: Invalid character '{}'",
                            *current as char
                        ),
                    ));
                }
                None => {
                    return Err(ParseError::Syntax(
                        self.bytes.current_pos,
                        "Error parsing infinity: Premature end of input".to_string(),
                    ));
                }
            }
        }

        duration_repr.is_infinite = true;
        match self.bytes.current_byte {
            Some(byte) if delimiter(*byte) => {
                self.try_consume_connection()?;

                match self.bytes.current_byte {
                    Some(_) => Ok((duration_repr, Some(self))),
                    None => Ok((duration_repr, None)),
                }
            }
            Some(byte) => Err(ParseError::Syntax(
                self.bytes.current_pos,
                format!(
                    "Error parsing infinity: Expected a delimiter but found '{}'",
                    *byte as char
                ),
            )),
            None => Ok((duration_repr, None)),
        }
    }

    #[inline]
    fn parse_keyword(
        &mut self,
        keywords: Option<&dyn TimeUnitsLike>,
    ) -> Result<Option<(TimeUnit, Multiplier)>, ParseError> {
        debug_assert!(keywords.is_some()); // cov:excl-line

        let delimiter = self.delimiter;
        let start = self.bytes.current_pos;
        self.bytes
            .advance_to(|byte: u8| delimiter(byte) || byte.is_ascii_digit());

        let keyword = self.bytes.get_current_str(start).map_err(|error| {
            ParseError::Syntax(
                start + error.valid_up_to(),
                "Invalid utf-8 when applying the delimiter".to_string(),
            )
        })?;
        match keywords.unwrap().get(keyword) {
            None => {
                self.bytes.reset(start);
                Ok(None)
            }
            some_time_unit => {
                if let Some(byte) = self.bytes.current_byte {
                    if delimiter(*byte) {
                        self.try_consume_connection()?;
                    }
                }
                Ok(some_time_unit)
            }
        }
    }

    #[inline]
    fn parse_time_unit(
        &mut self,
        config: &Config,
        time_units: &dyn TimeUnitsLike,
    ) -> Result<Option<(TimeUnit, Multiplier)>, ParseError> {
        // cov:excl-start
        debug_assert!(
            self.bytes.current_byte.is_some(),
            "Don't call this function without being sure there's at least 1 byte remaining"
        ); // cov:excl-stop

        let start = self.bytes.current_pos;
        match config.allow_ago {
            Some(ago_delimiter) => {
                self.bytes.advance_to(|byte: u8| {
                    ago_delimiter(byte) || (self.delimiter)(byte) || byte.is_ascii_digit()
                });
            }
            None => {
                self.bytes
                    .advance_to(|byte: u8| (self.delimiter)(byte) || byte.is_ascii_digit());
            }
        }
        let string = self.bytes.get_current_str(start).map_err(|error| {
            ParseError::TimeUnit(
                start + error.valid_up_to(),
                "Invalid utf-8 when applying the delimiter".to_string(),
            )
        })?;

        let (time_unit, mut multiplier) = if string.is_empty() {
            return Ok(None);
        } else {
            match time_units.get(string) {
                None => {
                    return Err(ParseError::TimeUnit(
                        start,
                        format!("Invalid time unit: '{string}'"),
                    ));
                }
                Some(some_time_unit) => some_time_unit,
            }
        };

        match (self.bytes.current_byte, config.allow_ago) {
            (Some(byte), Some(delimiter)) if delimiter(*byte) => {
                let start = self.bytes.current_pos;
                self.bytes.try_consume_delimiter(delimiter)?;
                if self.bytes.next_is_ignore_ascii_case(b"ago") {
                    // SAFETY: We know that next is `ago` which has 3 bytes
                    unsafe { self.bytes.advance_by(3) };
                    multiplier = multiplier.neg();
                } else {
                    self.bytes.reset(start);
                }
            }
            _ => {}
        }

        if let Some(byte) = self.bytes.current_byte {
            if (self.delimiter)(*byte) {
                self.try_consume_connection()?;
            }
        }

        Ok(Some((time_unit, multiplier)))
    }

    #[inline]
    fn parse_number_time_unit(
        &mut self,
        duration_repr: &mut DurationRepr<'a>,
        config: &Config,
        time_units: &dyn TimeUnitsLike,
    ) -> Result<bool, ParseError> {
        match self.bytes().current_byte {
            Some(_) if !time_units.is_empty() => {
                if let Some((unit, multi)) = self.parse_time_unit(config, time_units)? {
                    duration_repr.unit = unit;
                    duration_repr.multiplier = multi;
                }
            }
            Some(_) => {}
            None => return Ok(false),
        }
        Ok(true)
    }

    #[inline]
    fn finalize(&'a mut self, duration_repr: DurationRepr<'a>) -> Result<Self::Output, ParseError> {
        let delimiter = self.delimiter;
        match self.bytes().current_byte {
            Some(byte) if delimiter(*byte) => self
                .try_consume_connection()
                .map(|_| (duration_repr, Some(self))),
            Some(_) => Ok((duration_repr, Some(self))),
            None => Ok((duration_repr, None)),
        }
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;

    struct TimeUnitsFixture;

    // cov:excl-start This is just a fixture
    impl TimeUnitsLike for TimeUnitsFixture {
        fn is_empty(&self) -> bool {
            true
        }

        fn get(&self, _: &str) -> Option<(TimeUnit, Multiplier)> {
            None
        }
    } // cov:excl-stop

    #[rstest]
    #[case::zeros("00000000", Some(0x3030303030303030))]
    #[case::one("00000001", Some(0x3130303030303030))]
    #[case::ten_millions("10000000", Some(0x3030303030303031))]
    #[case::nines("99999999", Some(0x3939393939393939))]
    fn test_duration_repr_parser_parse_8_digits(
        #[case] input: &str,
        #[case] expected: Option<u64>,
    ) {
        let mut parser = ReprParserSingle::new(input);
        assert_eq!(parser.bytes.parse_8_digits(), expected);
    }

    #[rstest]
    #[case::empty("", None)]
    #[case::one_non_digit_char("a0000000", None)]
    #[case::less_than_8_digits("9999999", None)]
    fn test_duration_repr_parser_parse_8_digits_when_not_8_digits(
        #[case] input: &str,
        #[case] expected: Option<u64>,
    ) {
        let mut parser = ReprParserSingle::new(input);
        assert_eq!(parser.bytes.parse_8_digits(), expected);
        assert_eq!(parser.bytes.get_remainder(), input.as_bytes());
        assert_eq!(parser.bytes.current_byte, input.as_bytes().first());
        assert_eq!(parser.bytes.current_pos, 0);
    }

    #[test]
    fn test_duration_repr_parser_parse_8_digits_when_more_than_8() {
        let mut parser = ReprParserSingle::new("00000000a");
        assert_eq!(parser.bytes.parse_8_digits(), Some(0x3030303030303030));
        assert_eq!(parser.bytes.get_remainder(), &[b'a']);
        assert_eq!(parser.bytes.current_byte, Some(&b'a'));
        assert_eq!(parser.bytes.current_pos, 8);
    }

    #[rstest]
    #[case::zero("0", Whole(1, 1))]
    #[case::one("1", Whole(0, 1))]
    #[case::nine("9", Whole(0, 1))]
    #[case::ten("10", Whole(0, 2))]
    #[case::eight_leading_zeros("00000000", Whole(8, 8))]
    #[case::fifteen_leading_zeros("000000000000000", Whole(15, 15))]
    #[case::ten_with_leading_zeros_when_eight_digits("00000010", Whole(6, 8))]
    #[case::ten_with_leading_zeros_when_nine_digits("000000010", Whole(7, 9))]
    #[case::mixed_number("12345", Whole(0, 5))]
    #[case::max_8_digits("99999999", Whole(0, 8))]
    #[case::max_8_digits_minus_one("99999998", Whole(0, 8))]
    #[case::min_nine_digits("100000000", Whole(0, 9))]
    #[case::min_nine_digits_plus_one("100000001", Whole(0, 9))]
    #[case::eight_zero_digits_start("0000000011111111", Whole(8, 16))]
    #[case::eight_zero_digits_end("1111111100000000", Whole(0, 16))]
    #[case::eight_zero_digits_middle("11111111000000001", Whole(0, 17))]
    #[case::max_16_digits("9999999999999999", Whole(0, 16))]
    fn test_duration_repr_parser_parse_whole(#[case] input: &str, #[case] expected: Whole) {
        let mut parser = ReprParserSingle::new(input);
        assert_eq!(parser.parse_whole(), expected);

        let mut parser = ReprParserMultiple::new(input, |byte| byte == b' ', &[]);
        assert_eq!(parser.parse_whole(), expected);
    }

    // TODO: add test case for parse_multiple
    #[test]
    fn test_duration_repr_parser_parse_whole_when_more_than_max_exponent() {
        let config = Config::new();
        let input = &"1".repeat(i16::MAX as usize + 100);
        let mut parser = ReprParserSingle::new(input);
        let duration_repr = parser.parse(&config, &TimeUnitsFixture, None).unwrap();
        assert_eq!(duration_repr.whole, Some(Whole(0, i16::MAX as usize + 100)));
        assert_eq!(duration_repr.fract, None);
    }

    // TODO: use own test case for parse_multiple
    #[test]
    fn test_duration_repr_parser_parse_fract_when_more_than_max_exponent() {
        let input = format!(".{}", "1".repeat(i16::MAX as usize + 100));
        let config = Config::new();

        let mut parser = ReprParserSingle::new(&input);
        let duration_repr = parser.parse(&config, &TimeUnitsFixture, None).unwrap();
        assert_eq!(duration_repr.whole, None);
        assert_eq!(duration_repr.fract, Some(Fract(1, i16::MAX as usize + 101)));

        let mut config = Config::new();
        let delimiter = |byte| byte == b' ';
        config.parse_multiple_delimiter = Some(delimiter);
        let mut parser = ReprParserMultiple::new(&input, delimiter, &[]);
        let (duration_repr, maybe_parser) = parser.parse(&config, &TimeUnitsFixture, None).unwrap();
        assert!(maybe_parser.is_none());
        assert_eq!(duration_repr.whole, None);
        assert_eq!(duration_repr.fract, Some(Fract(1, i16::MAX as usize + 101)));
    }

    #[rstest]
    #[case::zero("0", Fract(0, 1))]
    #[case::one("1", Fract(0, 1))]
    #[case::nine("9", Fract(0, 1))]
    #[case::ten("10", Fract(0, 2))]
    #[case::leading_zero("01", Fract(0, 2))]
    #[case::leading_zeros("001", Fract(0, 3))]
    #[case::eight_leading_zeros("000000001", Fract(0, 9))]
    #[case::mixed_number("12345", Fract(0, 5))]
    #[case::max_8_digits("99999999", Fract(0, 8))]
    #[case::max_8_digits_minus_one("99999998", Fract(0, 8))]
    #[case::nine_digits("123456789", Fract(0, 9))]
    fn test_duration_repr_parser_parse_fract(#[case] input: &str, #[case] expected: Fract) {
        let mut parser = ReprParserSingle::new(input);
        assert_eq!(parser.parse_fract(), expected);

        let mut parser = ReprParserMultiple::new(input, |byte| byte == b' ', &[]);
        assert_eq!(parser.parse_fract(), expected);
    }
}
