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

/// Transform a string with length <= 16 into a u64 array representing a lowercase ascii array
///
/// Each element in the u64 array represents an ascii character array of 8 bytes. This method
/// enables a fast case insensitive comparison of strings. The maximum size of 16 is chosen
/// deliberately because gnu's time units, keywords and numerals all have a lower size.
pub(crate) const fn to_lowercase_u64(string: &str) -> [u64; 2] {
    const LOWER_CASE_MASK: [u64; 9] = [
        0x0,
        0x0000_0000_0000_0020,
        0x0000_0000_0000_2020,
        0x0000_0000_0020_2020,
        0x0000_0000_2020_2020,
        0x0000_0020_2020_2020,
        0x0000_2020_2020_2020,
        0x0020_2020_2020_2020,
        0x2020_2020_2020_2020,
    ];

    // cov:excl-start
    debug_assert!(
        string.len() <= 16,
        "This method only supports string lengths <= 16"
    ); // cov:excl-stop

    let mut dest: [u64; 2] = [0; 2];

    let bytes_ptr = string.as_bytes().as_ptr();
    let dest_ptr = dest.as_ptr() as *mut u8;
    if string.len() > 8 {
        // SAFETY: The memory regions are nonoverlapping. It is safe to read 8 bytes from the source
        // and write the same amount into `dest`. Both, the source and dest are properly aligned.
        unsafe { bytes_ptr.copy_to_nonoverlapping(dest_ptr, 8) }
        dest[0] = u64::from_le(dest[0]) | LOWER_CASE_MASK[8];

        // SAFETY: The memory regions are nonoverlapping. It is safe to read string.len() - 8 bytes
        // from the source and write the same amount into `dest`. Both, the source and dest
        // are properly aligned.
        unsafe {
            bytes_ptr
                .add(8)
                .copy_to_nonoverlapping(dest_ptr.add(8), string.len() - 8);
        }
        dest[1] = u64::from_le(dest[1]) | LOWER_CASE_MASK[string.len() - 8];
    } else {
        // SAFETY: The memory regions are nonoverlapping. It is safe to read string.len() bytes from
        // the source and write the same amount into `dest`. Both, the source and dest are properly
        // aligned.
        unsafe { bytes_ptr.copy_to_nonoverlapping(dest_ptr, string.len()) }
        dest[0] = u64::from_le(dest[0]) | LOWER_CASE_MASK[string.len()];
    }

    dest
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::*;

    #[rstest]
    #[case::empty("", [0, 0])]
    #[case::one_char("a", [0x0000_0000_0000_0061, 0])]
    #[case::one_char_big("A", [0x0000_0000_0000_0061, 0])]
    #[case::two_chars("az", [0x0000_0000_0000_7A61, 0])]
    #[case::two_chars_big("AZ", [0x0000_0000_0000_7A61, 0])]
    #[case::two_chars_mixed("aZ", [0x0000_0000_0000_7A61, 0])]
    #[case::eight_chars("abcdefgh", [0x6867_6665_6463_6261, 0])]
    #[case::eight_chars_big("ABCDEFGH", [0x6867_6665_6463_6261, 0])]
    #[case::eight_chars_mixed("ABcdEfGh", [0x6867_6665_6463_6261, 0])]
    #[case::nine_chars("abcdefghi", [0x6867_6665_6463_6261, 0x0000_0000_0000_0069])]
    #[case::nine_chars_big("ABCDEFGHI", [0x6867_6665_6463_6261, 0x0000_0000_0000_0069])]
    #[case::nine_chars_mixed("ABcDefGHi", [0x6867_6665_6463_6261, 0x0000_0000_0000_0069])]
    #[case::sixteen_chars("abcdefghijklmnop", [0x6867_6665_6463_6261, 0x706F_6E6D_6C6B_6A69])]
    #[case::sixteen_chars_big("ABCDEFGHIJKLMNOP", [0x6867_6665_6463_6261, 0x706F_6E6D_6C6B_6A69])]
    #[case::sixteen_chars_mixed("aBcDeFGHijKlMnoP", [0x6867_6665_6463_6261, 0x706F_6E6D_6C6B_6A69])]
    fn test_to_lowercase_u64(#[case] string: &str, #[case] expected: [u64; 2]) {
        let res = to_lowercase_u64(string);
        assert_eq!(res, expected, "0x{:016x} 0x{:016x}", res[0], res[1]);
    }

    #[rstest]
    #[case::now("now", [0x0000_0000_0077_6F6E, 0])]
    #[case::yesterday("yesterday", [0x6164_7265_7473_6579, 0x0000_0000_0000_0079])]
    #[case::tomorrow("tomorrow", [0x776F_7272_6F6D_6F74, 0])]
    #[case::today("today", [0x0000_0079_6164_6F74, 0])]
    #[case::sec("sec", [0x0000_0000_0063_6573, 0])]
    #[case::secs("secs", [0x0000_0000_7363_6573, 0])]
    #[case::second("second", [0x0000_646E_6F63_6573, 0])]
    #[case::seconds("seconds", [0x0073_646E_6F63_6573, 0])]
    #[case::min("min", [0x0000_0000_006E_696D, 0])]
    #[case::mins("mins", [0x0000_0000_736E_696D, 0])]
    #[case::minute("minute", [0x0000_6574_756E_696D, 0])]
    #[case::minutes("minutes", [0x0073_6574_756E_696D, 0])]
    #[case::hour("hour", [0x0000_0000_7275_6F68, 0])]
    #[case::hours("hours", [0x0000_0073_7275_6F68, 0])]
    #[case::day("day", [0x0000_0000_0079_6164, 0])]
    #[case::days("days", [0x0000_0000_7379_6164, 0])]
    #[case::week("week", [0x0000_0000_6B65_6577, 0])]
    #[case::weeks("weeks", [0x0000_0073_6B65_6577, 0])]
    #[case::fortnight("fortnight", [0x6867_696e_7472_6f66, 0x0000_0000_0000_0074])]
    #[case::fortnights("fortnights", [0x6867_696e_7472_6f66, 0x0000_0000_0000_7374])]
    #[case::month("month", [0x0000_0068_746E_6F6D, 0])]
    #[case::months("months", [0x0000_7368_746E_6F6D, 0])]
    #[case::year("year", [0x0000_0000_7261_6579, 0])]
    #[case::last("last", [0x0000_0000_7473_616C, 0])]
    #[case::this("this", [0x0000_0000_7369_6874, 0])]
    #[case::next("next", [0x0000_0000_7478_656E, 0])]
    #[case::first("first", [0x0000_0074_7372_6966, 0])]
    #[case::third("third", [0x0000_0064_7269_6874, 0])]
    #[case::fourth("fourth", [0x0000_6874_7275_6F66, 0])]
    #[case::fifth("fifth", [0x0000_0068_7466_6966, 0])]
    #[case::sixth("sixth", [0x0000_0068_7478_6973, 0])]
    #[case::seventh("seventh", [0x0068_746E_6576_6573, 0])]
    #[case::eighth("eighth", [0x0000_6874_6867_6965, 0])]
    #[case::ninth("ninth", [0x0000_0068_746E_696E, 0])]
    #[case::tenth("tenth", [0x0000_0068_746E_6574, 0])]
    #[case::eleventh("eleventh", [0x6874_6E65_7665_6C65, 0])]
    #[case::twelfth("twelfth", [0x0068_7466_6C65_7774, 0])]
    fn test_to_lowercase_u64_with_all_gnu_ids(#[case] string: &str, #[case] expected: [u64; 2]) {
        let res = to_lowercase_u64(string);
        assert_eq!(res, expected, "0x{:016x} 0x{:016x}", res[0], res[1]);
    }
}
