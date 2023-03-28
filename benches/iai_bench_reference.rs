// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use iai_callgrind::{black_box, main};

const SMALL_INPUT: &str = "1";

#[inline(never)]
#[export_name = "__iai_setup::generate_large_input"]
fn generate_large_input() -> String {
    let ones = "1".repeat(1022);
    format!("{}.{}e-1022", &ones, &ones)
}

#[inline(never)]
fn small_reference() -> Duration {
    Duration::from_secs_f64(black_box(SMALL_INPUT).parse().unwrap())
}

#[inline(never)]
fn large_reference() -> Duration {
    Duration::from_secs_f64(black_box(generate_large_input()).parse().unwrap())
}

main!(
    callgrind_args =
        "toggle-collect=iai_callgrind::black_box",
        "toggle-collect=__iai_setup::generate_large_input";
    functions = small_reference, large_reference
);
