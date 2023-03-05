// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use iai::black_box;
use std::time::Duration;

const LARGE_INPUT: &str =
    "11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111.\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111111111111111111111\
    11111111111111111111111111111111111111111111111111111111111111e-1022";
const SMALL_INPUT: &str = "1";

#[inline(never)]
fn small_reference() {
    let _ = Duration::from_secs_f64(black_box(SMALL_INPUT).parse().unwrap());
}

#[inline(never)]
fn large_reference() {
    let _ = Duration::from_secs_f64(black_box(LARGE_INPUT).parse().unwrap());
}

iai::main!(small_reference, large_reference);
