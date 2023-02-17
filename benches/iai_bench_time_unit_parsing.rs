// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::DurationParser;
use iai::black_box;

const SMALL_INPUT: &str = "1";
const SMALL_INPUT_SECONDS: &str = "1s";
const SMALL_INPUT_MICRO_SECONDS: &str = "1Ms";

fn no_time_unit() {
    let _ = DurationParser::new().parse(black_box(SMALL_INPUT));
}

fn time_unit_length_1() {
    let _ = DurationParser::new().parse(black_box(SMALL_INPUT_SECONDS));
}

fn time_unit_length_2() {
    let _ = DurationParser::new().parse(black_box(SMALL_INPUT_MICRO_SECONDS));
}

iai::main!(no_time_unit, time_unit_length_1, time_unit_length_2);
