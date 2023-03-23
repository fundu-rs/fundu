// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! This module is the working horse of the parser. Public interfaces to the parser are located in
//! the main library `lib.rs`.

use std::cmp::Ordering::{Equal, Greater, Less};
use std::time::Duration;

use crate::builder::config::Config;
use crate::error::ParseError;
use crate::time::{Duration as FunduDuration, Multiplier, TimeUnit, TimeUnitsLike};

const ATTO_MULTIPLIER: u64 = 1_000_000_000_000_000_000;
const ATTO_TO_NANO: u64 = 1_000_000_000;

const POW10: [u64; 20] = [
    1,
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
    10_000_000_000,
    100_000_000_000,
    1_000_000_000_000,
    10_000_000_000_000,
    100_000_000_000_000,
    1_000_000_000_000_000,
    10_000_000_000_000_000,
    100_000_000_000_000_000,
    1_000_000_000_000_000_000,
    10_000_000_000_000_000_000,
];

trait Parse8Digits {
    // This method is based on the work of Johnny Lee and his blog post
    // https://johnnylee-sde.github.io/Fast-numeric-string-to-int
    #[inline]
    unsafe fn parse_8_digits(digits: &[u8]) -> u64 {
        // cov:excl-start
        debug_assert!(
            digits.len() >= 8,
            "Call this method only if digits has length >= 8"
        ); // cov:excl-stop

        let ptr = digits.as_ptr() as *const u64;
        let mut num = u64::from_le(ptr.read_unaligned());
        num = (num.wrapping_mul(2561)) >> 8;
        num = ((num & 0x00FF00FF00FF00FF).wrapping_mul(6553601)) >> 16;
        num = ((num & 0x0000FFFF0000FFFF).wrapping_mul(42949672960001)) >> 32;
        num
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
struct Whole(usize);

impl Parse8Digits for Whole {}

impl Whole {
    #[inline]
    fn parse_slice(digits: &[u8]) -> Result<u64, ParseError> {
        let mut seconds = 0u64;
        let mut iter = digits.chunks_exact(8);
        for digits in iter.by_ref() {
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
                .and_then(|s| s.checked_add(*num as u64))
            {
                Some(s) => seconds = s,
                None => {
                    return Err(ParseError::Overflow);
                }
            }
        }
        Ok(seconds)
    }

    #[inline]
    fn parse(&self, digits: &[u8], zeroes: Option<usize>) -> Result<u64, ParseError> {
        if digits.is_empty() {
            return Ok(0);
        }

        let seconds = Self::parse_slice(digits)?;
        if seconds == 0 {
            Ok(0)
        } else {
            match zeroes {
                Some(num_zeroes) if num_zeroes > 0 => match POW10.get(num_zeroes) {
                    Some(pow) => Ok(seconds.saturating_mul(*pow)),
                    None => Err(ParseError::Overflow),
                },
                Some(_) | None => Ok(seconds),
            }
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.0
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
struct Fract(usize, usize);

impl Parse8Digits for Fract {}

impl Fract {
    #[inline]
    fn parse_slice(mut multi: u64, zeroes: usize, digits: &[u8]) -> u64 {
        let mut attos = 0;
        let len = digits.len();

        if multi >= 100_000_000 && len >= 8 {
            let max = 18usize.saturating_sub(zeroes);
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
                attos += *num as u64 * multi;
            }
        } else if multi > 0 && len > 0 {
            for num in digits {
                multi /= 10;
                if multi == 0 {
                    return attos;
                }
                attos += *num as u64 * multi;
            }
            // else would be reached if multi or len are zero but these states are already handled
            // in parse
        } // cov:excl-line
        attos
    }

    #[inline]
    fn parse(&self, digits: &[u8], zeroes: Option<usize>) -> u64 {
        if digits.is_empty() {
            return 0;
        }

        let num_zeroes = zeroes.unwrap_or_default();
        let multi = ATTO_MULTIPLIER / POW10.get(num_zeroes).unwrap_or(&u64::MAX);
        if multi == 0 {
            return 0;
        }

        Self::parse_slice(multi, num_zeroes, digits)
    }

    #[inline]
    fn len(&self) -> usize {
        self.1 - self.0
    }
}

#[derive(Debug, Default)]
pub(crate) struct DurationRepr {
    unit: TimeUnit,
    number_is_optional: bool,
    is_negative: bool,
    is_infinite: bool,
    whole: Option<Whole>,
    fract: Option<Fract>,
    digits: Option<Vec<u8>>,
    exponent: i16,
    multiplier: Multiplier,
}

impl DurationRepr {
    #[inline]
    pub(crate) fn parse(&mut self) -> Result<FunduDuration, ParseError> {
        if self.is_infinite {
            return Ok(FunduDuration::new(self.is_negative, Duration::MAX));
        }

        let (whole, fract) = match (self.whole.take(), self.fract.take()) {
            (None, None) if self.number_is_optional => {
                self.digits = Some(vec![1]);
                (Whole(1), Fract(1, 1))
            }
            (None, None) => unreachable!(), // cov:excl-line
            (None, Some(fract)) => (Whole(0), fract),
            (Some(whole), None) => {
                let fract_start_and_end = whole.len();
                (whole, Fract(fract_start_and_end, fract_start_and_end))
            }
            (Some(whole), Some(fract)) => (whole, fract),
        };

        // This unwrap is safe because there is at least whole or fract
        let digits = self.digits.as_ref().unwrap();

        let Multiplier(multiplier, mut exponent) = self.unit.multiplier() * self.multiplier;
        exponent += self.exponent as i32;

        // The maximum absolute value of the exponent is `abs(i16::MIN) + 9 (nano seconds)`, so it
        // is safe to cast to usize
        let exponent_abs: usize = exponent.unsigned_abs().try_into().unwrap();

        // We're operating on slices to minimize runtime costs. Applying the exponent before parsing
        // to integers is necessary, since the exponent can move digits into the to be considered
        // final integer domain.
        let (seconds, attos) = match exponent.cmp(&0) {
            Less if whole.len() > exponent_abs => {
                let (whole_part, fract_part) = digits.split_at(whole.len() - exponent_abs);
                let seconds = whole.parse(whole_part, None);
                let attos = if seconds.is_ok() {
                    Some(fract.parse(fract_part, None))
                } else {
                    None
                };
                (Some(seconds), attos)
            }
            Less => {
                let attos = Some(fract.parse(digits, Some(exponent_abs - whole.len())));
                (None, attos)
            }
            Equal => {
                let (whole_part, fract_part) = digits.split_at(whole.len());
                let seconds = whole.parse(whole_part, None);
                let attos = if seconds.is_ok() {
                    Some(fract.parse(fract_part, None))
                } else {
                    None
                };
                (Some(seconds), attos)
            }
            Greater if fract.len() > exponent_abs => {
                let (whole_part, fract_part) = digits.split_at(fract.0 + exponent_abs);
                let seconds = whole.parse(whole_part, None);
                let attos = if seconds.is_ok() {
                    Some(fract.parse(fract_part, None))
                } else {
                    None
                };
                (Some(seconds), attos)
            }
            Greater => {
                let seconds = whole.parse(digits, Some(exponent_abs - fract.len()));
                (Some(seconds), None)
            }
        };

        // Finally, parse the seconds and atto seconds and interpret a seconds overflow as
        // maximum `Duration`.
        let (seconds, attos) = match seconds {
            Some(result) => match result {
                Ok(seconds) => (seconds, attos.unwrap_or_default()),
                Err(ParseError::Overflow) => {
                    return Ok(FunduDuration::new(self.is_negative, Duration::MAX));
                }
                // only ParseError::Overflow is returned by `Seconds::parse`
                Err(_) => unreachable!(), // cov:excl-line
            },
            None => (0, attos.unwrap_or_default()),
        };

        // allow -0 or -0.0 etc., or in general numbers x with abs(x) < 1e-18 and interpret them
        // as zero duration
        if seconds == 0 && attos == 0 {
            Ok(FunduDuration::new(false, Duration::ZERO))
        } else if multiplier == 1 {
            Ok(FunduDuration::new(
                self.is_negative,
                Duration::new(seconds, (attos / ATTO_TO_NANO) as u32),
            ))
        } else {
            let attos = attos as u128 * (multiplier as u128);
            Ok(
                match seconds
                    .checked_mul(multiplier)
                    .and_then(|s| s.checked_add((attos / (ATTO_MULTIPLIER as u128)) as u64))
                {
                    Some(s) => FunduDuration::new(
                        self.is_negative,
                        Duration::new(s, ((attos / (ATTO_TO_NANO as u128)) % 1_000_000_000) as u32),
                    ),
                    None => FunduDuration::new(self.is_negative, Duration::MAX),
                },
            )
        }
    }
}

pub(crate) struct ReprParser<'a> {
    current_pos: usize, // keep first. Has better performance.
    current_byte: Option<&'a u8>,
    config: &'a Config,
    time_units: &'a dyn TimeUnitsLike,
    input: &'a [u8],
}

/// Parse a source string into a [`DurationRepr`].
impl<'a> ReprParser<'a> {
    #[inline]
    pub fn new(input: &'a str, config: &'a Config, time_units: &'a dyn TimeUnitsLike) -> Self {
        let input = input.as_bytes();
        Self {
            current_byte: input.first(),
            input,
            current_pos: 0,
            time_units,
            config,
        }
    }

    #[inline]
    fn advance(&mut self) {
        self.current_pos += 1;
        self.current_byte = self.input.get(self.current_pos);
    }

    #[inline]
    fn get_remainder(&self) -> &[u8] {
        &self.input[self.current_pos..]
    }

    #[inline]
    fn finish(&mut self) {
        self.current_pos += self.get_remainder().len();
        self.current_byte = None
    }

    /// This method is based on the work of Daniel Lemire and his blog post
    /// <https://lemire.me/blog/2018/09/30/quickly-identifying-a-sequence-of-digits-in-a-string-of-characters/>
    #[inline]
    fn is_8_digits(&self) -> bool {
        self.input
            .get(self.current_pos..(self.current_pos + 8))
            .map_or(false, |digits| {
                let ptr = digits.as_ptr() as *const u64;
                // SAFETY: We just ensured there are 8 bytes
                let num = u64::from_le(unsafe { ptr.read_unaligned() });
                (num & (num.wrapping_add(0x0606060606060606)) & 0xf0f0f0f0f0f0f0f0)
                    == 0x3030303030303030
            })
    }

    #[inline]
    unsafe fn advance_by(&mut self, num: usize) {
        self.current_pos += num;
        self.current_byte = self.input.get(self.current_pos);
    }

    #[inline]
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
                    Some(num - 0x3030303030303030)
                } else {
                    None
                }
            })
    }

    #[inline]
    pub(crate) fn parse(&'a mut self) -> Result<DurationRepr, ParseError> {
        if self.current_byte.is_none() {
            return Err(ParseError::Empty);
        }

        let Config {
            allow_spaces,
            default_unit,
            default_multiplier: _,
            disable_exponent,
            disable_fraction,
            max_exponent,
            min_exponent,
            number_is_optional,
        } = *self.config;

        let mut duration_repr = DurationRepr {
            unit: default_unit,
            number_is_optional,
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
                // the maximum number of digits that need to be considered depending on the
                // exponent: max(-exponent) = abs(i16::MIN) + max_digits(u64::MAX) =
                // 20 + 9 (nano seconds) + 1 + alignment at modulo 8
                let max = ((min_exponent as isize).abs() + 32) as usize;

                // // Using `len()` is a rough (but always correct) estimation for an upper bound.
                // // However, using maybe more memory than needed spares the costly memory
                // reallocations
                duration_repr.digits = Some(Vec::with_capacity(
                    max.min(self.input.len() - self.current_pos),
                ));
                duration_repr.whole = duration_repr
                    .digits
                    .as_mut()
                    .map(|digits| self.parse_whole(digits));
            }
            Some(byte) if *byte == b'.' || number_is_optional => {}
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
                ));
            }
        }

        // parse the fraction number part of the input
        match self.current_byte {
            Some(byte) if *byte == b'.' && !disable_fraction => {
                self.advance();
                let fract = match self.current_byte {
                    Some(byte) if byte.is_ascii_digit() => {
                        let needed = self.input.len() - self.current_pos;
                        let digits = match duration_repr.digits.as_mut() {
                            Some(digits) if digits.capacity() - digits.len() >= needed => digits,
                            Some(digits) => {
                                let max = (max_exponent as usize) + 25;
                                digits
                                    .try_reserve_exact(max.min(needed))
                                    .expect("Failed to allocate memory");
                                digits
                            }
                            None => {
                                let max = (max_exponent as usize) + 25;
                                duration_repr.digits = Some(Vec::with_capacity(max.min(needed)));
                                duration_repr.digits.as_mut().unwrap()
                            }
                        };
                        Some(self.parse_fract(digits))
                    }
                    Some(_) | None if duration_repr.whole.is_none() => {
                        return Err(ParseError::Syntax(
                            self.current_pos,
                            "Either the whole number part or the fraction must be present"
                                .to_string(),
                        ));
                    }
                    Some(_) => None,
                    None => return Ok(duration_repr),
                };
                duration_repr.fract = fract;
            }
            Some(byte) if *byte == b'.' => {
                return Err(ParseError::Syntax(
                    self.current_pos,
                    "No fraction allowed".to_string(),
                ));
            }
            Some(_) => {}
            None => return Ok(duration_repr),
        }

        // TODO: what about time units starting with an 'e'??
        // parse the exponent of the input if present
        match self.current_byte {
            Some(byte) if byte.eq_ignore_ascii_case(&b'e') && !disable_exponent => {
                self.advance();
                duration_repr.exponent = self.parse_exponent()?;
            }
            Some(byte) if byte.eq_ignore_ascii_case(&b'e') => {
                return Err(ParseError::Syntax(
                    self.current_pos,
                    "No exponent allowed".to_string(),
                ));
            }
            Some(_) => {}
            None => return Ok(duration_repr),
        }

        // If there are spaces between the number and the time unit, the spaces are consumed or an
        // error is returned depending on the configuration value for `allow_spaces`
        match self.current_byte {
            Some(byte) if *byte == b' ' => {
                if allow_spaces {
                    self.advance();
                    self.consume_spaces();
                } else {
                    return Err(ParseError::Syntax(
                        self.current_pos,
                        "No spaces allowed".to_string(),
                    ));
                }
            }
            Some(_) => {}
            None => return Ok(duration_repr),
        }

        // parse the time unit if present
        match self.current_byte {
            Some(_) if !self.time_units.is_empty() => {
                let (unit, multi) = self.parse_time_unit()?;
                duration_repr.unit = unit;
                duration_repr.multiplier = multi;
            }
            Some(byte) => {
                return Err(ParseError::TimeUnit(
                    self.current_pos,
                    format!("No time units allowed but found: '{}'", *byte as char),
                ));
            }
            None => return Ok(duration_repr),
        }

        // check we've reached the end of input
        match self.current_byte {
            Some(_) => unreachable!("Parsing time units consumes the rest of the input"), /* cov:excl-line */
            None => Ok(duration_repr),
        }
    }

    #[inline]
    fn consume_spaces(&mut self) {
        while let Some(byte) = self.current_byte {
            if *byte == b' ' {
                self.advance()
            } else {
                break;
            }
        }
    }

    #[inline]
    fn parse_time_unit(&mut self) -> Result<(TimeUnit, Multiplier), ParseError> {
        // cov:excl-start
        debug_assert!(
            self.current_byte.is_some(),
            "Don't call this function without being sure there's at least 1 byte remaining"
        ); // cov:excl-stop

        // SAFETY: The input of `parse` is &str and therefore valid utf-8 and we have read only
        // ascii characters up to this point.
        let string = unsafe { std::str::from_utf8_unchecked(self.get_remainder()) };
        let result = self.time_units.get(string).ok_or_else(|| {
            ParseError::TimeUnit(self.current_pos, format!("Invalid time unit: '{string}'"))
        });
        self.finish();
        result
    }

    #[inline]
    fn parse_whole(&mut self, digits: &mut Vec<u8>) -> Whole {
        debug_assert!(
            self.current_byte
                .map_or(false, |byte| byte.is_ascii_digit())
        );

        let mut capacity = digits.capacity();
        let mut strip_leading_zeroes = true;
        if capacity >= 8 && self.is_8_digits() {
            let mut counter = 0;
            let ptr = digits.as_ptr() as *mut u64;
            while let Some(eight) = self.parse_8_digits() {
                if capacity >= 8 && (!strip_leading_zeroes || eight != 0) {
                    // SAFETY: We just ensured there is enough capacity in the vector
                    unsafe { *ptr.add(counter) = u64::from_le(eight) }
                    counter += 1;
                    strip_leading_zeroes = false;
                    capacity -= 8;
                }
            }

            // SAFETY: counter * 8 results always within the reserved space for the vector.
            unsafe { digits.set_len(counter << 3) }
        // capacity is smaller than 8 or there are no 8 digits
        } else {
            let digit = self.current_byte.unwrap() - b'0';
            if digit != 0 {
                digits.push(digit);
                strip_leading_zeroes = false;
            }
            self.advance();
        }

        while let Some(byte) = self.current_byte {
            let digit = byte.wrapping_sub(b'0');
            if digit < 10 {
                if capacity > 0 && (!strip_leading_zeroes || digit != 0) {
                    digits.push(digit);
                    strip_leading_zeroes = false;
                    // no capacity decrement needed since `max` is aligned at modulo 8
                }
                self.advance();
            } else {
                break;
            }
        }

        Whole(digits.len())
    }

    #[inline]
    fn parse_fract(&mut self, digits: &mut Vec<u8>) -> Fract {
        debug_assert!(
            self.current_byte
                .map_or(false, |byte| byte.is_ascii_digit())
        );

        let mut capacity = digits.capacity() - digits.len();
        let start = digits.len();
        if capacity >= 8 && self.is_8_digits() {
            let mut counter = 0;
            let mut ptr = digits.as_ptr() as *const u8;
            unsafe { ptr = ptr.add(start) };
            let ptr = ptr as *mut u64;
            while let Some(eight) = self.parse_8_digits() {
                if capacity >= 8 {
                    // SAFETY: We just ensured capacity >= 8
                    unsafe { *ptr.add(counter) = u64::from_le(eight) }
                    counter += 1;
                    capacity -= 8;
                }
            }

            // SAFETY: counter * 8 results always within the reserved space for the vector.
            unsafe { digits.set_len(start + (counter << 3)) }
        } else {
            let digit = self.current_byte.unwrap() - b'0';
            digits.push(digit);
            self.advance();
        }

        while let Some(byte) = self.current_byte {
            let digit = byte.wrapping_sub(b'0');
            if digit < 10 {
                if capacity > 0 {
                    digits.push(digit);
                    // no capacity decrement needed
                }
                self.advance();
            } else {
                break;
            }
        }

        Fract(start, digits.len())
    }

    #[inline]
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
                    ));
                }
                None if pos == 3 => return Ok(()), // short `inf` is allowed
                None => {
                    return Err(ParseError::Syntax(
                        self.current_pos,
                        "Unexpected end of input".to_string(),
                    ));
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
    #[inline]
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

    #[inline]
    fn parse_exponent(&mut self) -> Result<i16, ParseError> {
        let is_negative = self.parse_sign_is_negative()?;
        self.current_byte.ok_or_else(|| {
            ParseError::Syntax(
                self.current_pos,
                "Expected exponent but reached end of input".to_string(),
            )
        })?;

        let mut exponent = 0i16;
        while let Some(byte) = self.current_byte {
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
                self.advance();
            } else {
                break;
            }
        }

        Ok(exponent)
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
    #[case::zeroes("00000000")]
    #[case::nines("99999999")]
    #[case::mixed("012345678")]
    #[case::more_than_8_digits("0123456789")]
    fn test_duration_repr_parse_is_8_digits_when_8_digits(#[case] input: &str) {
        let config = Config::new();
        let parser = ReprParser::new(input, &config, &TimeUnitsFixture);
        assert!(parser.is_8_digits());
    }

    #[rstest]
    #[case::empty("")]
    #[case::less_than_8("0000000")]
    #[case::all_forward_slash("////////")] // '/' = 0x2F one below '0'
    #[case::all_double_point("::::::::")] // ':' = 0x3A one above '9'
    #[case::one_not_digit("a0000000")]
    fn test_duration_repr_parse_is_8_digits_when_not_8_digits(#[case] input: &str) {
        let config = Config::new();
        let parser = ReprParser::new(input, &config, &TimeUnitsFixture);
        assert!(!parser.is_8_digits());
    }

    #[rstest]
    #[case::zeros("00000000", Some(0x0000000000000000))]
    #[case::one("00000001", Some(0x0100000000000000))]
    #[case::ten_millions("10000000", Some(0x0000000000000001))]
    #[case::nines("99999999", Some(0x0909090909090909))]
    fn test_duration_repr_parser_parse_8_digits(
        #[case] input: &str,
        #[case] expected: Option<u64>,
    ) {
        let config = Config::new();
        let mut parser = ReprParser::new(input, &config, &TimeUnitsFixture);
        assert_eq!(parser.parse_8_digits(), expected);
    }

    #[rstest]
    #[case::empty("", None)]
    #[case::one_non_digit_char("a0000000", None)]
    #[case::less_than_8_digits("9999999", None)]
    fn test_duration_repr_parser_parse_8_digits_when_not_8_digits(
        #[case] input: &str,
        #[case] expected: Option<u64>,
    ) {
        let config = Config::new();
        let mut parser = ReprParser::new(input, &config, &TimeUnitsFixture);
        assert_eq!(parser.parse_8_digits(), expected);
        assert_eq!(parser.get_remainder(), input.as_bytes());
        assert_eq!(parser.current_byte, input.as_bytes().first());
        assert_eq!(parser.current_pos, 0);
    }

    #[test]
    fn test_duration_repr_parser_parse_8_digits_when_more_than_8() {
        let config = Config::new();
        let mut parser = ReprParser::new("00000000a", &config, &TimeUnitsFixture);
        assert_eq!(parser.parse_8_digits(), Some(0));
        assert_eq!(parser.get_remainder(), &[b'a']);
        assert_eq!(parser.current_byte, Some(&b'a'));
        assert_eq!(parser.current_pos, 8);
    }

    #[rstest]
    #[case::zero("0", vec![])]
    #[case::one("1", vec![1])]
    #[case::nine("9", vec![9])]
    #[case::ten("10", vec![1,0])]
    #[case::eight_leading_zeroes("00000000", vec![])]
    #[case::fifteen_leading_zeroes("000000000000000", vec![])]
    #[case::ten_with_leading_zeros_when_eight_digits("00000010", vec![0,0,0,0,0,0,1,0])]
    #[case::ten_with_leading_zeros_when_nine_digits("000000010", vec![0,0,0,0,0,0,0,1,0])]
    #[case::mixed_number("12345", vec![1,2,3,4,5])]
    #[case::max_8_digits("99999999", vec![9,9,9,9,9,9,9,9])]
    #[case::max_8_digits_minus_one("99999998", vec![9,9,9,9,9,9,9,8])]
    #[case::min_nine_digits("100000000", vec![1,0,0,0,0,0,0,0,0])]
    #[case::min_nine_digits_plus_one("100000001", vec![1,0,0,0,0,0,0,0,1])]
    #[case::eight_zero_digits_start("0000000011111111", vec![1,1,1,1,1,1,1,1])]
    #[case::eight_zero_digits_end("1111111100000000", vec![1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0])]
    #[case::eight_zero_digits_middle("11111111000000001", vec![1,1,1,1,1,1,1,1,0,0,0,0,0,0,0,0,1])]
    #[case::max_16_digits("9999999999999999", vec![9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9])]
    fn test_duration_repr_parser_parse_whole(
        #[case] input: &str,
        #[case] expected_digits: Vec<u8>,
    ) {
        let config = Config::new();
        let mut parser = ReprParser::new(input, &config, &TimeUnitsFixture);
        let mut digits = Vec::with_capacity(input.len());
        assert_eq!(parser.parse_whole(&mut digits), Whole(digits.len()));
        assert_eq!(digits, expected_digits);
    }

    #[test]
    fn test_duration_repr_parser_parse_whole_when_more_than_max() {
        let config = Config::new();
        let input = &"1".repeat(i16::MAX as usize + 100);
        let expected = vec![1u8; i16::MAX as usize + 33];
        let mut parser = ReprParser::new(input, &config, &TimeUnitsFixture);
        assert_eq!(parser.parse().unwrap().digits.unwrap(), expected);
    }

    #[test]
    fn test_duration_repr_parser_parse_fract_when_more_than_max() {
        let input = format!(".{}", "1".repeat(i16::MAX as usize + 100));
        let expected = vec![1u8; i16::MAX as usize + 25];
        let config = Config::new();
        let mut parser = ReprParser::new(&input, &config, &TimeUnitsFixture);
        let result = parser.parse().unwrap();
        let digits = result.digits.unwrap();
        assert_eq!(digits.len(), expected.len());
        assert_eq!(digits, expected);
    }

    #[rstest]
    #[case::zero("0", vec![0])]
    #[case::one("1", vec![1])]
    #[case::nine("9", vec![9])]
    #[case::ten("10", vec![1,0])]
    #[case::leading_zero("01", vec![0,1])]
    #[case::leading_zeroes("001", vec![0,0,1])]
    #[case::eight_leading_zeros("000000001", vec![0,0,0,0,0,0,0,0,1])]
    #[case::mixed_number("12345", vec![1,2,3,4,5])]
    #[case::max_8_digits("99999999", vec![9,9,9,9,9,9,9,9])]
    #[case::max_8_digits_minus_one("99999998", vec![9,9,9,9,9,9,9,8])]
    #[case::nine_digits("123456789", vec![1,2,3,4,5,6,7,8,9])]
    fn test_duration_repr_parser_parse_fract(#[case] input: &str, #[case] expected: Vec<u8>) {
        let config = Config::new();
        let mut parser = ReprParser::new(input, &config, &TimeUnitsFixture);
        let mut digits = Vec::with_capacity(input.len());
        assert_eq!(parser.parse_fract(&mut digits), Fract(0, input.len()));
        assert_eq!(digits, expected)
    }
}
