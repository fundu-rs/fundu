// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

//! fundu together with chrono
//!
//! Chrono::Duration has different limits compared to rust std::time::Duration. This example shows
//! how to saturate the parsed std::time::Duration at the maximum of Chrono::Duration instead of
//! std::time::Duration::MAX and then convert the result to a Chrono::Duration.

// TODO: Completely rewrite this example to directly convert from fundu's duration into chrono
// duration
use chrono::Duration as ChronoDuration;
use fundu::DurationParser;

fn main() {
    let std_duration = TryInto::<std::time::Duration>::try_into(
        DurationParser::new()
        // Use an arbitrary but high number as input, so the `fundu` parser saturates at
        // `std::time::Duration::MAX`
        .parse(&format!("{}.999999999", f64::MAX))
        // Usually you'd want to do some error handling but here we know that our input won't
        // produce any errors
        .unwrap(),
    )
    .unwrap()
    .min(ChronoDuration::max_value().to_std().unwrap());

    println!("{}", ChronoDuration::from_std(std_duration).unwrap());
}
