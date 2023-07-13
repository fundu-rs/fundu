// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu_gnu::{Duration, ParseError, RelativeTimeParser};
use iai_callgrind::{black_box, main};

type Result<T> = std::result::Result<T, ParseError>;

const ONE_SEC: &str = "1sec";
const SEC: &str = "sec";
const ONE_SECONDS: &str = "1seconds";
const SECONDS: &str = "seconds";
const ONE_MIN: &str = "1min";
const MIN: &str = "min";
const ONE_MINUTES: &str = "1minutes";
const MINUTES: &str = "minutes";
const DAY: &str = "day";
const ONE_DAY: &str = "1day";

#[inline(never)]
#[export_name = "__iai_setup::setup_parser"]
fn setup_parser<'a>() -> RelativeTimeParser<'a> {
    RelativeTimeParser::new()
}

#[inline(never)]
fn one_sec() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(ONE_SEC))
}

#[inline(never)]
fn sec() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(SEC))
}

#[inline(never)]
fn one_seconds() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(ONE_SECONDS))
}

#[inline(never)]
fn seconds() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(SECONDS))
}

#[inline(never)]
fn one_min() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(ONE_MIN))
}

#[inline(never)]
fn min() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(MIN))
}

#[inline(never)]
fn one_minutes() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(ONE_MINUTES))
}

#[inline(never)]
fn minutes() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(MINUTES))
}

#[inline(never)]
fn one_day() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(ONE_DAY))
}

#[inline(never)]
fn day() -> Result<Duration> {
    let parser = setup_parser();
    black_box(parser).parse(black_box(DAY))
}

main!(
    callgrind_args = "toggle-collect=iai_callgrind::black_box",
        "toggle-collect=__iai_setup::setup_parser";
    functions = sec,
    one_sec,
    seconds,
    one_seconds,
    min,
    one_min,
    minutes,
    one_minutes,
    day,
    one_day,
);
