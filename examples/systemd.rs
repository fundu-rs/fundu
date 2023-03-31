// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! A systemd time parser as specified in `man systemd.time`. The output is imitating
//! the output of `systemd-analyze timespan SYSTEMD_TIME_SPAN`

use std::time::Duration;

use clap::{command, Arg};
use fundu::{CustomDurationParser, SYSTEMD_TIME_UNITS};

/// Create a human readable string like `100y 2h 46min 40s 123us 456ns` from a `Duration`
fn make_human(duration: Duration) -> String {
    const YEAR: u64 = 31557600;
    const MONTH: u64 = 2629800;
    const WEEK: u64 = 604800;
    const DAY: u64 = 86400;
    const HOUR: u64 = 3600;
    const MINUTE: u64 = 60;
    const MILLIS_PER_NANO: u32 = 1_000_000;
    const MICROS_PER_NANO: u32 = 1_000;

    if duration.is_zero() {
        return "0".to_string();
    }

    let mut result = Vec::with_capacity(10);
    let mut secs = duration.as_secs();
    if secs > 0 {
        if secs >= YEAR {
            result.push(format!("{}y", secs / YEAR));
            secs %= YEAR;
        }
        if secs >= MONTH {
            result.push(format!("{}month", secs / MONTH));
            secs %= MONTH;
        }
        if secs >= WEEK {
            result.push(format!("{}w", secs / WEEK));
            secs %= WEEK;
        }
        if secs >= DAY {
            result.push(format!("{}d", secs / DAY));
            secs %= DAY;
        }
        if secs >= HOUR {
            result.push(format!("{}h", secs / HOUR));
            secs %= HOUR;
        }
        if secs >= MINUTE {
            result.push(format!("{}min", secs / MINUTE));
            secs %= MINUTE;
        }
        if secs >= 1 {
            result.push(format!("{}s", secs));
        }
    }

    let mut nanos = duration.subsec_nanos();
    if nanos > 0 {
        if nanos >= MILLIS_PER_NANO {
            result.push(format!("{}ms", nanos / MILLIS_PER_NANO));
            nanos %= MILLIS_PER_NANO;
        }
        if nanos >= MICROS_PER_NANO {
            result.push(format!("{}us", nanos / MICROS_PER_NANO));
            nanos %= MICROS_PER_NANO;
        }
        if nanos >= 1 {
            result.push(format!("{}ns", nanos));
        }
    }

    result.join(" ")
}

fn main() {
    let matches = command!()
        .allow_negative_numbers(true)
        .arg(Arg::new("SYSTEMD_TIME_SPAN").action(clap::ArgAction::Set))
        .get_matches();

    let delimiter = |byte| matches!(byte, b' ' | b'\t' | b'\n' | b'\r');
    let parser = CustomDurationParser::builder()
        .time_units(&SYSTEMD_TIME_UNITS)
        .disable_exponent()
        .disable_fraction()
        .disable_infinity()
        .allow_delimiter(delimiter)
        .parse_multiple(delimiter)
        .build();

    let input: &String = matches
        .get_one("SYSTEMD_TIME_SPAN")
        .expect("At least one argument must be present");
    match parser.parse(input.trim()) {
        Ok(duration) => {
            println!("{:>8}: {}", "Original", input);
            let (secs, micros) = (duration.as_secs(), duration.subsec_micros());
            if secs == 0 && micros == 0 {
                println!("{:>8}: 0", "μs");
            } else {
                println!("{:>8}: {secs}{micros}", "μs",);
            }
            println!("{:>8}: {}", "Human", make_human(duration));
        }
        Err(error) => eprintln!("Failed to parse time span '{}': {}", &input, error),
    }
}
