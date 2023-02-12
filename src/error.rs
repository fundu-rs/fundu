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
    /// Syntax error
    Syntax(usize, String),
    /// Overflow error
    Overflow,
    /// Errors concerning time units
    TimeUnit(usize, String),
    /// A generic error if no other error type fits
    InvalidInput(String),
    NegativeExponentOverflow,
    PositiveExponentOverflow,
    NegativeNumber,
    NegativeInfinity,
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
            ParseError::InvalidInput(reason) => format!("Invalid input: {reason}"),
            ParseError::NegativeExponentOverflow => "Negative exponent overflow".to_string(),
            ParseError::PositiveExponentOverflow => "Positive exponent overflow".to_string(),
            ParseError::NegativeNumber => "Number was negative".to_string(),
            ParseError::NegativeInfinity => "Infinity was negative".to_string(),
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
    #[case::time_unit_error(ParseError::TimeUnit(10, "Found invalid 'y'".to_string()), "Time unit error: Found invalid 'y' at column 10")]
    #[case::invalid_input(
        ParseError::InvalidInput("Unexpected".to_string()),
        "Invalid input: Unexpected"
    )]
    fn test_error_messages(#[case] error: ParseError, #[case] expected: &str) {
        assert_eq!(error.to_string(), expected);
    }
}
