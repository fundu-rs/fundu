// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::SystemTime;

pub(crate) const fn floor_div(lhs: i64, rhs: i64) -> i64 {
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
pub(crate) fn now() -> SystemTime {
    SystemTime::now()
}
// cov:excl-stop

#[cfg(any(miri, test))]
pub(crate) fn now() -> SystemTime {
    SystemTime::UNIX_EPOCH
}

// This is a faster alternative to str::trim_matches. We're exploiting that we're using the posix
// definition of whitespace which only contains ascii characters as whitespace
pub(crate) fn trim_whitespace(source: &str) -> &str {
    let mut bytes = source.as_bytes();
    while let Some((byte, remainder)) = bytes.split_first() {
        if byte == &b' ' || byte.wrapping_sub(9) < 5 {
            bytes = remainder;
        } else {
            break;
        }
    }
    while let Some((byte, remainder)) = bytes.split_last() {
        if byte == &b' ' || byte.wrapping_sub(9) < 5 {
            bytes = remainder;
        } else {
            break;
        }
    }
    // SAFETY: We've trimmed only ascii characters and therefore valid utf-8
    unsafe { std::str::from_utf8_unchecked(bytes) }
}
