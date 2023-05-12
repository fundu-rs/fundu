// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::{Duration, DurationParser, ParseError};
use iai_callgrind::{black_box, main};

type Result<T> = std::result::Result<T, ParseError>;

const SMALL_NEGATIVE_INPUT: &str = "-1";
const MIXED_NEGATIVE_INPUT_7: &str = "-1234567.1234567";
const MIXED_NEGATIVE_INPUT_8: &str = "-12345678.12345678";

#[inline(never)]
#[export_name = "__iai_setup::setup_parser"]
fn setup_parser<'a>() -> DurationParser<'a> {
    DurationParser::builder().allow_negative().build()
}

#[inline(never)]
#[export_name = "__iai_setup::generate_large_input"]
fn generate_large_input() -> String {
    let ones = "1".repeat(1022);
    format!("-{}.{}e-1022", &ones, &ones)
}

#[inline(never)]
fn small_negative_input() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(SMALL_NEGATIVE_INPUT))
}

#[inline(never)]
fn mixed_negative_input_7() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(MIXED_NEGATIVE_INPUT_7))
}

#[inline(never)]
fn mixed_negative_input_8() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(MIXED_NEGATIVE_INPUT_8))
}

#[inline(never)]
fn large_negative_input() -> Result<Duration> {
    let parser = setup_parser();
    let input = generate_large_input();
    black_box(parser).parse(black_box(&input))
}

main!(
    callgrind_args =
        "toggle-collect=iai_callgrind::black_box",
        "toggle-collect=__iai_setup::setup_parser",
        "toggle-collect=__iai_setup::generate_large_input";
    functions =
        small_negative_input,
        mixed_negative_input_7,
        mixed_negative_input_8,
        large_negative_input,
);
