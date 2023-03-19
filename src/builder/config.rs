// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use crate::{time::DEFAULT_TIME_UNIT, TimeUnit};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Config {
    pub allow_spaces: bool,
    pub default_unit: TimeUnit,
}

impl Config {
    pub const fn new() -> Self {
        Self {
            allow_spaces: false,
            default_unit: DEFAULT_TIME_UNIT,
        }
    }
}
