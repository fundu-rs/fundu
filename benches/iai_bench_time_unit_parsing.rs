// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use fundu::{DurationParser, ParseError};
use iai_callgrind::{black_box, main};

type Result<T> = std::result::Result<T, ParseError>;

const SMALL_INPUT: &str = "1";
const SMALL_INPUT_SECONDS: &str = "1s";
const SMALL_INPUT_MICRO_SECONDS: &str = "1Ms";

#[inline(never)]
fn no_time_unit() -> Result<Duration> {
    DurationParser::new().parse(black_box(SMALL_INPUT))
}

#[inline(never)]
fn time_unit_length_1() -> Result<Duration> {
    DurationParser::new().parse(black_box(SMALL_INPUT_SECONDS))
}

#[inline(never)]
fn time_unit_length_2() -> Result<Duration> {
    DurationParser::new().parse(black_box(SMALL_INPUT_MICRO_SECONDS))
}

main!(no_time_unit, time_unit_length_1, time_unit_length_2);
