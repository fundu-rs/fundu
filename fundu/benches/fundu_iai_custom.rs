// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::{CustomDurationParser, DEFAULT_ALL_TIME_UNITS, SYSTEMD_TIME_UNITS};
use iai_callgrind::{black_box, main};

#[inline(never)]
fn initialization_with_default_time_units<'a>() -> CustomDurationParser<'a> {
    CustomDurationParser::with_time_units(black_box(&DEFAULT_ALL_TIME_UNITS))
}

#[inline(never)]
fn initialization_with_systemd_time_units<'a>() -> CustomDurationParser<'a> {
    CustomDurationParser::with_time_units(black_box(&SYSTEMD_TIME_UNITS))
}

main!(
    callgrind_args =
        "toggle-collect=iai_callgrind::black_box";
    functions =
        initialization_with_default_time_units,
        initialization_with_systemd_time_units
);
