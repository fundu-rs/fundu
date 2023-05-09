// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! Provide the [`ParseError`]

use std::error::Error;
use std::fmt::Display;

/// Error type emitted during the parsing
#[derive(Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ParseError {
    /// Returned, if the input was empty.
    Empty,
    /// A syntax error. Syntax errors report the position (column) where it was encountered and a
    /// reason.
    Syntax(usize, String),
    /// Currently only used internally for overflows of the maximum Duration.
    Overflow,
    /// An error concerning time units. Like [`ParseError::Syntax`]  the position where the error
    /// occurred is included.
    TimeUnit(usize, String),
    /// The exponent exceeded the minimum negative exponent (`-32768`)
    NegativeExponentOverflow,
    /// The exponent exceeded the maximum positive exponent (`+32767`)
    PositiveExponentOverflow,
    /// The input number was negative. Note that numbers close to `0` (`< 1e-18) are not negative
    /// but resolve to `0`
    NegativeNumber,
    /// A generic error if no other error type fits
    InvalidInput(String),
}

impl Error for ParseError {}

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            ParseError::Syntax(column, reason) => {
                format!("Syntax error: {reason} at column {column}")
            }
            ParseError::Overflow => "Number overflow".to_string(),
            ParseError::TimeUnit(pos, reason) => {
                format!("Time unit error: {reason} at column {pos}")
            }
            ParseError::NegativeExponentOverflow => {
                "Negative exponent overflow: Minimum is -32768".to_string()
            }
            ParseError::PositiveExponentOverflow => {
                "Positive exponent overflow: Maximum is +32767".to_string()
            }
            ParseError::NegativeNumber => "Number was negative".to_string(),
            ParseError::InvalidInput(reason) => format!("Invalid input: {reason}"),
            ParseError::Empty => "Empty input".to_string(),
        };
        f.write_str(&msg)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TryFromDurationError {
    NegativeNumber,
    #[allow(dead_code)]
    PositiveOverflow,
    #[allow(dead_code)]
    NegativeOverflow,
}

impl From<TryFromDurationError> for ParseError {
    fn from(error: TryFromDurationError) -> Self {
        match error {
            TryFromDurationError::NegativeNumber => ParseError::NegativeNumber,
            TryFromDurationError::PositiveOverflow => ParseError::Overflow,
            TryFromDurationError::NegativeOverflow => ParseError::Overflow,
        }
    }
}

impl Error for TryFromDurationError {}

impl Display for TryFromDurationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let description = match self {
            TryFromDurationError::NegativeNumber => "Error converting duration: value is negative",
            TryFromDurationError::PositiveOverflow => {
                "Error converting duration: value overflows the positive value range"
            }
            TryFromDurationError::NegativeOverflow => {
                "Error converting duration: value overflows the negative value range"
            }
        };
        description.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;

    #[rstest]
    #[case::syntax_error(
        ParseError::Syntax(10, "Invalid character".to_string()),
        "Syntax error: Invalid character at column 10"
    )]
    #[case::overflow(ParseError::Overflow, "Number overflow")]
    #[case::time_unit_error(
        ParseError::TimeUnit(10, "Found invalid 'y'".to_string()),
        "Time unit error: Found invalid 'y' at column 10"
    )]
    #[case::negative_exponent_overflow_error(
        ParseError::NegativeExponentOverflow,
        "Negative exponent overflow: Minimum is -32768"
    )]
    #[case::positive_exponent_overflow_error(
        ParseError::PositiveExponentOverflow,
        "Positive exponent overflow: Maximum is +32767"
    )]
    #[case::negative_number_error(ParseError::NegativeNumber, "Number was negative")]
    #[case::invalid_input(
        ParseError::InvalidInput("Unexpected".to_string()),
        "Invalid input: Unexpected"
    )]
    #[case::empty(ParseError::Empty, "Empty input")]
    fn test_error_messages(#[case] error: ParseError, #[case] expected: &str) {
        assert_eq!(error.to_string(), expected);
    }

    #[rstest]
    #[case::negative_overflow(TryFromDurationError::NegativeOverflow, ParseError::Overflow)]
    #[case::positive_overflow(TryFromDurationError::PositiveOverflow, ParseError::Overflow)]
    #[case::negative_number(TryFromDurationError::NegativeNumber, ParseError::NegativeNumber)]
    fn test_from_for_parse_error(#[case] from: TryFromDurationError, #[case] expected: ParseError) {
        assert_eq!(ParseError::from(from), expected);
    }
}
