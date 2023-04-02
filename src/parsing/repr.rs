// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::cmp::Ordering::*;
use std::time::Duration;

use crate::time::Duration as FunduDuration;
use crate::{Multiplier, ParseError, TimeUnit};

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
pub(super) struct Whole(pub(super) usize);

impl Parse8Digits for Whole {}

impl Whole {
    #[inline]
    fn parse_slice(digits: &[u8]) -> Result<u64, ParseError> {
        let mut seconds = 0u64;
        if digits.len() >= 8 {
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
        } else {
            for num in digits {
                seconds = seconds * 10 + *num as u64
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
pub(super) struct Fract(pub(super) usize, pub(super) usize);

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
        let pow = match POW10.get(num_zeroes) {
            Some(pow) => pow,
            None => return 0,
        };
        let multi = ATTO_MULTIPLIER / pow;
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
pub(super) struct DurationRepr {
    pub(super) unit: TimeUnit,
    pub(super) number_is_optional: bool,
    pub(super) is_negative: bool,
    pub(super) is_infinite: bool,
    pub(super) whole: Option<Whole>,
    pub(super) fract: Option<Fract>,
    pub(super) digits: Option<Vec<u8>>,
    pub(super) exponent: i16,
    pub(super) multiplier: Multiplier,
}

impl DurationRepr {
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

        // This unwrap is safe because there are whole or fract present
        let digits = self.digits.as_ref().unwrap();

        let Multiplier(multiplier, exponent) = self.unit.multiplier() * self.multiplier;
        let exponent = exponent as i32 + self.exponent as i32;

        // The maximum absolute value of the exponent is `2 * abs(i16::MIN)`, so it is safe to cast
        // to usize
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
