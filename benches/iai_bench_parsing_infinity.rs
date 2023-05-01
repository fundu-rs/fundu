// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use fundu::{DurationParser, ParseError};
use iai_callgrind::{black_box, main};

type Result<T> = std::result::Result<T, ParseError>;

const SHORT_INF: &str = "inf";
const LONG_INFINITY: &str = "infinity";

#[inline(never)]
#[export_name = "__iai_setup::setup_parser"]
fn setup_parser() -> DurationParser {
    DurationParser::without_time_units()
}

#[inline(never)]
fn short_inf() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(SHORT_INF))
}

#[inline(never)]
fn long_infinity() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(LONG_INFINITY))
}

main!(
    callgrind_args = "toggle-collect=iai_callgrind::black_box",
    "toggle-collect=__iai_setup::setup_parser";
    functions =
        short_inf,
        long_infinity,
);
