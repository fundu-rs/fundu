// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use fundu::{DurationParser, ParseError};
use iai_callgrind::{black_box, main};

type Result<T> = std::result::Result<T, ParseError>;

const SMALL_INPUT: &str = "1";
const MIXED_INPUT_7: &str = "1234567.1234567";
const MIXED_INPUT_8: &str = "12345678.12345678";

#[inline(never)]
#[export_name = "__iai_setup::setup_parser"]
fn setup_parser() -> DurationParser {
    DurationParser::without_time_units()
}

#[inline(never)]
#[export_name = "__iai_setup::generate_large_input"]
fn generate_large_input() -> String {
    let ones = "1".repeat(1022);
    format!("{}.{}e-1022", &ones, &ones)
}

#[inline(never)]
fn small_input() -> Result<Duration> {
    black_box(setup_parser()).parse(black_box(SMALL_INPUT))
}

#[inline(never)]
fn mixed_input_7() -> Result<Duration> {
    black_box(setup_parser()).parse(black_box(MIXED_INPUT_7))
}

#[inline(never)]
fn mixed_input_8() -> Result<Duration> {
    black_box(setup_parser()).parse(black_box(MIXED_INPUT_8))
}

#[inline(never)]
fn large_input() -> Result<Duration> {
    let input = black_box(generate_large_input());
    black_box(setup_parser()).parse(&input)
}

main!(
    callgrind_args =
        "toggle-collect=__iai_setup::setup_parser",
        "toggle-collect=__iai_setup::generate_large_input";
    functions =
        small_input,
        mixed_input_7,
        mixed_input_8,
        large_input,
);
