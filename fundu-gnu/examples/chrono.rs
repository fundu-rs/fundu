// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! A small command line application which uses clap for parsing the arguments and chrono as an
//! example for converting fundu's duration into another duration.

use clap::{command, Arg};
use fundu_gnu::{parse, SaturatingInto, TryFromDurationError};

fn main() {
    let matches = command!()
        .about(
            "A gnu relative time parser as specified in `info '(coreutils) Relative items in \
             date'`.",
        )
        .allow_negative_numbers(true)
        .allow_hyphen_values(true)
        .arg(
            Arg::new("GNU_RELATIVE_TIME")
                .action(clap::ArgAction::Set)
                .help(
                    "A relative time as specified in `info '(coreutils) Relative items in date \
                     strings'`",
                ),
        )
        .get_matches();

    let input: &String = matches
        .get_one("GNU_RELATIVE_TIME")
        .expect("One argument must be present");
    match parse(input) {
        Ok(duration) => {
            println!("{:>42}: {}", "Original", input);
            let chrono_duration: chrono::Duration = duration.saturating_into();
            println!(
                "{:>42}: {}",
                "Seconds (saturating_into chrono::Duration)",
                chrono_duration.num_seconds()
            );
            let chrono_duration: Result<chrono::Duration, TryFromDurationError> =
                duration.try_into();
            println!(
                "{:>42}: {}",
                "Seconds (try_into chrono::Duration)",
                match chrono_duration {
                    Ok(duration) => duration.num_seconds().to_string(),
                    Err(error) => error.to_string(),
                }
            );
        }
        Err(error) => eprintln!("Failed to parse relative time '{}': {}", &input, error),
    }
}
