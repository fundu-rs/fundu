// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::{Duration, ParseError};
use fundu_systemd::TimeSpanParser;
use iai_callgrind::{black_box, main};

type Result<T> = std::result::Result<T, ParseError>;

const INPUT_NO_TIME_UNIT: &str = "1";
const INPUT_NANO_SECOND: &str = "ns";
const INPUT_SECOND: &str = "s";
const INPUT_MINUTES: &str = "minutes";
const INPUT_YEAR: &str = "y";

#[inline(never)]
#[export_name = "__iai_setup::setup_parser"]
fn setup_parser<'a>() -> TimeSpanParser<'a> {
    TimeSpanParser::new()
}

#[inline(never)]
fn parsing_when_no_time_unit() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(INPUT_NO_TIME_UNIT))
}

#[inline(never)]
fn parsing_nano_second() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse_nanos(black_box(INPUT_NANO_SECOND))
}

#[inline(never)]
fn parsing_second() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(INPUT_SECOND))
}

#[inline(never)]
fn parsing_year() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(INPUT_YEAR))
}

#[inline(never)]
fn parsing_minutes() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(INPUT_MINUTES))
}

main!(
    callgrind_args =
        "toggle-collect=iai_callgrind::black_box",
        "toggle-collect=__iai_setup::setup_parser";
    functions =
        parsing_when_no_time_unit,
        parsing_nano_second,
        parsing_second,
        parsing_year,
        parsing_minutes
);
