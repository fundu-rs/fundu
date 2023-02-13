// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! Provide the [`ParseError`]

use std::error::Error;
use std::fmt::Display;

/// Error type emitted during the parsing
#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    /// A syntax error. Syntax errors report the position (column) where it was encountered and a
    /// reason.
    Syntax(usize, String),
    /// Currently only used internally for overflows of the maximum Duration.
    Overflow,
    /// An error concerning time units. Like [`ParseError::Syntax`]  the position where the error
    /// occurred is included.
    TimeUnit(usize, String),
    /// The exponent exceeded the minimum negative exponent (`-1022`)
    NegativeExponentOverflow,
    /// The exponent exceeded the maximum positive exponent (`+1023`)
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
                "Negative exponent overflow: Minimum is -1022".to_string()
            }
            ParseError::PositiveExponentOverflow => {
                "Positive exponent overflow: Maximum is +1023".to_string()
            }
            ParseError::NegativeNumber => "Number was negative".to_string(),
            ParseError::InvalidInput(reason) => format!("Invalid input: {reason}"),
        };
        f.write_str(&msg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

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
        "Negative exponent overflow: Minimum is -1022"
    )]
    #[case::positive_exponent_overflow_error(
        ParseError::PositiveExponentOverflow,
        "Positive exponent overflow: Maximum is +1023"
    )]
    #[case::negative_number_error(ParseError::NegativeNumber, "Number was negative")]
    #[case::invalid_input(
        ParseError::InvalidInput("Unexpected".to_string()),
        "Invalid input: Unexpected"
    )]
    fn test_error_messages(#[case] error: ParseError, #[case] expected: &str) {
        assert_eq!(error.to_string(), expected);
    }
}
