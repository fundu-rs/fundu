// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::DurationParser;
use fundu::TimeUnit::{self, *};
use iai_callgrind::{black_box, main};

#[inline(never)]
#[export_name = "__iai_setup::get_all_time_units"]
fn get_all_time_units<'a>() -> &'a [TimeUnit] {
    &[
        NanoSecond,
        MicroSecond,
        MilliSecond,
        Second,
        Minute,
        Hour,
        Day,
        Week,
        Month,
        Year,
    ]
}

#[inline(never)]
fn initialization_without_time_units<'a>() -> DurationParser<'a> {
    DurationParser::without_time_units()
}

#[inline(never)]
fn initialization_with_default_time_units<'a>() -> DurationParser<'a> {
    DurationParser::new()
}

#[inline(never)]
fn initialization_with_all_time_units<'a>() -> DurationParser<'a> {
    DurationParser::with_all_time_units()
}

#[inline(never)]
fn initialization_with_custom_time_units<'a>() -> DurationParser<'a> {
    DurationParser::with_time_units(black_box(get_all_time_units()))
}

main!(
    callgrind_args =
        "toggle-collect=iai_callgrind::black_box",
        "toggle-collect=__iai_setup::get_all_time_units";
    functions =
        initialization_without_time_units,
        initialization_with_default_time_units,
        initialization_with_all_time_units,
        initialization_with_custom_time_units,
);
