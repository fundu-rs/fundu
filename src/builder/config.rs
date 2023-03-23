// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use crate::time::{Multiplier, DEFAULT_TIME_UNIT};
use crate::TimeUnit;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Config {
    pub allow_spaces: bool,
    pub default_unit: TimeUnit,
    pub default_multiplier: Multiplier,
    pub disable_exponent: bool,
    pub disable_fraction: bool,
    pub number_is_optional: bool,
    pub max_exponent: i16,
    pub min_exponent: i16,
}

impl Config {
    pub const fn new() -> Self {
        Self {
            allow_spaces: false,
            default_unit: DEFAULT_TIME_UNIT,
            default_multiplier: Multiplier(1, 0),
            disable_exponent: false,
            disable_fraction: false,
            number_is_optional: false,
            max_exponent: i16::MAX,
            min_exponent: i16::MIN,
        }
    }
}
