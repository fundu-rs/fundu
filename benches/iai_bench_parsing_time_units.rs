// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::TimeUnit::{self, *};
use fundu::{Duration, DurationParser, ParseError};
use iai_callgrind::{black_box, main};

type Result<T> = std::result::Result<T, ParseError>;

const INPUT_NO_TIME_UNIT: &str = "1";
const INPUT_NANO_SECOND: &str = "1ns";
const INPUT_SECOND: &str = "1y";
const INPUT_YEAR: &str = "1y";

#[inline(never)]
#[export_name = "__iai_setup::setup_parser_with_all_time_units"]
fn setup_parser_with_all_time_units(default_unit: TimeUnit) -> DurationParser {
    let mut parser = DurationParser::with_all_time_units();
    parser.default_unit(default_unit);
    parser
}

#[inline(never)]
fn parsing_nano_second_when_no_time_unit() -> Result<Duration> {
    let time_unit = black_box(NanoSecond);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(INPUT_NO_TIME_UNIT))
}

#[inline(never)]
fn parsing_nano_second_when_time_unit() -> Result<Duration> {
    let time_unit = black_box(NanoSecond);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(INPUT_NANO_SECOND))
}

#[inline(never)]
fn parsing_second_when_no_time_unit() -> Result<Duration> {
    let time_unit = black_box(Second);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(INPUT_NO_TIME_UNIT))
}

#[inline(never)]
fn parsing_second_when_time_unit() -> Result<Duration> {
    let time_unit = black_box(Second);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(INPUT_SECOND))
}

#[inline(never)]
fn parsing_year_when_no_time_unit() -> Result<Duration> {
    let time_unit = black_box(Year);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(INPUT_NO_TIME_UNIT))
}

#[inline(never)]
fn parsing_year_when_time_unit() -> Result<Duration> {
    let time_unit = black_box(Year);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(INPUT_YEAR))
}

main!(
    callgrind_args =
        "toggle-collect=iai_callgrind::black_box",
        "toggle-collect=__iai_setup::setup_parser_with_all_time_units";
    functions =
        parsing_nano_second_when_no_time_unit,
        parsing_nano_second_when_time_unit,
        parsing_second_when_no_time_unit,
        parsing_second_when_time_unit,
        parsing_year_when_no_time_unit,
        parsing_year_when_time_unit
);
