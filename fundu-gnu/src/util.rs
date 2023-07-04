// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::SystemTime;

pub const fn floor_div(lhs: i64, rhs: i64) -> i64 {
    let d = lhs / rhs;
    let r = lhs % rhs;
    if (r > 0 && rhs < 0) || (r < 0 && rhs > 0) {
        d - 1
    } else {
        d
    }
}

// cov:excl-start
#[inline]
#[cfg(all(not(test), not(miri)))]
pub fn now() -> SystemTime {
    SystemTime::now()
}
// cov:excl-stop

#[cfg(any(miri, test))]
pub fn now() -> SystemTime {
    SystemTime::UNIX_EPOCH
}

/// TODO: document
#[macro_export]
macro_rules! validate {
    ($id:ident, $min:expr, $max:expr) => {{
        #[allow(unused_comparisons)]
        if $id < $min || $id > $max {
            panic!(concat!(
                "Invalid ",
                stringify!($id),
                ": Valid range is ",
                stringify!($min),
                " <= ",
                stringify!($id),
                " <= ",
                stringify!($max)
            ));
        }
    }};

    ($id:ident <= $max:expr) => {{
        #[allow(unused_comparisons)]
        if $id > $max {
            panic!(concat!(
                "Invalid ",
                stringify!($id),
                ": Valid maximum ",
                stringify!($id),
                " is ",
                stringify!($max)
            ));
        }
    }};
}
