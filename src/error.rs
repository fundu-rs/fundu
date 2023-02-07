// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! Provide the [`ParseError`]

use std::{error::Error, fmt::Display};

/// Error type emitted during the parsing
#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    /// Syntax error
    Syntax(usize, String),
    /// Overflow error
    Overflow,
    /// Errors concerning time units
    TimeUnitError,
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
            ParseError::TimeUnitError => "Invalid time unit".to_string(),
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
    #[case::time_unit_error(ParseError::TimeUnitError, "Invalid time unit")]
    #[case::invalid_input(
        ParseError::InvalidInput("Unexpected".to_string()),
        "Invalid input: Unexpected"
    )]
    fn test_error_messages(#[case] error: ParseError, #[case] expected: &str) {
        assert_eq!(error.to_string(), expected);
    }
}
