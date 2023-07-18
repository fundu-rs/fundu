// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::TimeUnit::{self, *};
use fundu::{Duration, DurationParser, DurationParserBuilder};
use iai_callgrind::{black_box, main};

const ONE: &str = "1";
const ONE_NANO_SECOND: &str = "1ns";
const NANO_SECOND: &str = "ns";
const ONE_SECOND: &str = "1s";
const SECOND: &str = "s";
const ONE_YEAR: &str = "1y";
const YEAR: &str = "y";

#[inline(never)]
#[export_name = "__iai_setup::setup_parser_with_all_time_units"]
fn setup_parser_with_all_time_units<'a>(default_unit: TimeUnit) -> DurationParser<'a> {
    DurationParserBuilder::new()
        .all_time_units()
        .default_unit(default_unit)
        .number_is_optional()
        .build()
}

#[inline(never)]
fn parsing_one_when_default_is_nano_second() -> Duration {
    let time_unit = black_box(NanoSecond);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(ONE)).unwrap()
}

#[inline(never)]
fn parsing_one_nano_second() -> Duration {
    let time_unit = black_box(NanoSecond);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(ONE_NANO_SECOND)).unwrap()
}

#[inline(never)]
fn parsing_nano_second() -> Duration {
    let time_unit = black_box(NanoSecond);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(NANO_SECOND)).unwrap()
}

#[inline(never)]
fn parsing_one_when_default_is_second() -> Duration {
    let time_unit = black_box(Second);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(ONE)).unwrap()
}

#[inline(never)]
fn parsing_one_second() -> Duration {
    let time_unit = black_box(Second);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(ONE_SECOND)).unwrap()
}

#[inline(never)]
fn parsing_second() -> Duration {
    let time_unit = black_box(Second);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(SECOND)).unwrap()
}

#[inline(never)]
fn parsing_one_when_default_is_year() -> Duration {
    let time_unit = black_box(Year);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(ONE)).unwrap()
}

#[inline(never)]
fn parsing_one_year() -> Duration {
    let time_unit = black_box(Year);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(ONE_YEAR)).unwrap()
}

#[inline(never)]
fn parsing_year() -> Duration {
    let time_unit = black_box(Year);
    let parser = setup_parser_with_all_time_units(time_unit);
    black_box(parser).parse(black_box(YEAR)).unwrap()
}

main!(
    callgrind_args =
        "toggle-collect=iai_callgrind::black_box",
        "toggle-collect=__iai_setup::setup_parser_with_all_time_units";
    functions =
    parsing_one_when_default_is_nano_second,
    parsing_one_nano_second,
    parsing_nano_second,
    parsing_one_when_default_is_second,
    parsing_one_second,
    parsing_second,
    parsing_one_when_default_is_year,
    parsing_one_year,
    parsing_year,
);
