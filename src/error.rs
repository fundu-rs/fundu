// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::fmt::Display;

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    Syntax(usize, String),
    Overflow,
    TimeUnitError,
    InvalidInput(String),
}

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
