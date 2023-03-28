// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use crate::time::{Multiplier, DEFAULT_TIME_UNIT};
use crate::TimeUnit;

pub type Delimiter = fn(u8) -> bool;

#[derive(Debug, PartialEq, Eq, Clone)]
pub(crate) struct Config {
    pub(crate) allow_delimiter: Option<Delimiter>,
    pub(crate) default_unit: TimeUnit,
    pub(crate) default_multiplier: Multiplier,
    pub(crate) disable_exponent: bool,
    pub(crate) disable_fraction: bool,
    pub(crate) number_is_optional: bool,
    pub(crate) max_exponent: i16,
    pub(crate) min_exponent: i16,
}

impl Default for Config {
    fn default() -> Self {
        Self::new()
    }
}

impl Config {
    pub(crate) const fn new() -> Self {
        Self {
            allow_delimiter: None,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_for_config() {
        assert_eq!(Config::default(), Config::new());
    }
}
