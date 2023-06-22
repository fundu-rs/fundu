<!--
 Copyright (c) 2023 Joining7943 <joining@posteo.de>

 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<h1 align="center">Fast and precise gnu relative time parser of rust strings to a Duration</h1>
<div align="center">
    <a href="https://docs.rs/crate/fundu-gnu/">fundu-gnu Docs</a>
    |
    <a href="https://github.com/Joining7943/fundu/blob/main/CHANGELOG.md">Changelog</a>
</div>
<br>
<div align="center">
    <a href="https://github.com/Joining7943/fundu/actions">
        <img src="https://github.com/Joining7943/fundu/actions/workflows/cicd.yml/badge.svg" alt="GitHub branch checks state"/>
    </a>
    <a href="https://codecov.io/gh/Joining7943/fundu" >
        <img src="https://codecov.io/gh/Joining7943/fundu/branch/main/graph/badge.svg?token=7GOQ1A6UPH"/>
    </a>
    <a href="https://crates.io/crates/fundu-gnu">
        <img src="https://img.shields.io/crates/v/fundu-gnu.svg" alt="Crates.io"/>
    </a>
    <a href="https://docs.rs/fundu-gnu/">
        <img src="https://docs.rs/fundu-gnu/badge.svg" alt="docs.rs"/>
    </a>
    <a href="https://github.com/rust-lang/rust">
        <img src="https://img.shields.io/badge/MSRV-1.64.0-brightgreen" alt="MSRV"/>
    </a>
</div>

## Table of Contents

- [Table of Contents](#table-of-contents)
    - [Overview](#overview)
    - [Audience](#audience)
    - [Installation](#installation)
    - [Format description](#description-of-the-format)
    - [Benchmarks](#benchmarks)
    - [License](#license)

# Overview

This crate provides a simple to use and fast parser based on [fundu](../README.md) aiming for full compatibility with
the [gnu](https://www.gnu.org/) relative items in date strings format as specified in
their [documentation].

`fundu-gnu` can parse rust strings like

| `&str` | Duration |
| -- | -- |
| `"1hour"`| `Duration::positive(60 * 60, 0)` |
| `"minute"`| `Duration::positive(60, 0)` |
| `"2 hours"`| `Duration::positive(2 * 60 * 60, 0)` |
| `"1year 12months"`| `Duration::positive(63_115_200, 0)` |
| `"-3minutes"`| `Duration::negative(3 * 60, 0)` |
| `"3 mins ago"`| `Duration::negative(3 * 60, 0)` |
| `"999sec +1day"`| `Duration::positive(86_400 + 999, 0)` |
| `"55secs500week"`| `Duration::positive(55 + 500 * 604_800, 0)` |
| `"123456789"`| `Duration::positive(123_456_789, 0)` |
| `"42fortnight"`| `Duration::positive(42 * 2 * 604_800, 0)` |
| `"yesterday"`| `Duration::negative(24 * 60 * 60, 0)` |
| `"now"`| `Duration::positive(0, 0)` |
| `"today -10seconds"`| `Duration::negative(10, 0)` |
| `"1000000000000000000000000000000000000years"`| `Duration::MAX` |

Note that `fundu` parses into its own `Duration` which is a superset of other `Durations` like
[`std::time::Duration`], [`chrono::Duration`] and [`time::Duration`]. See the
[documentation](https://docs.rs/fundu/latest/fundu/index.html#fundus-duration) how to easily handle
the conversion between these durations. For a full description of this crate see the
[docs](https://docs.rs/fundu-gnu/latest/fundu-gnu)!

# Audience

This crate is for you if you

- seek a fast and reliable gnu compatible duration parser
- want it to simply just work without diving into many customizations
- just like the gnu format
- ...

This crate might not be for you if you want to customize the parser to a format which would not be
compatible with `gnu`. See the main [fundu](../README.md) project, if you want to use a parser
tailored to your needs.

# Installation

Add this to `Cargo.toml`

```toml
[dependencies]
fundu-gnu = "0.1.0"
```

or install with `cargo add fundu-gnu`.

Activating the `chrono` or `time` feature provides a `TryFrom` implementation for
[`chrono::Duration`] or [`time::Duration`]. Converting from/to [`std::time::Duration`] does not require
an additional feature. Activating the `serde` feature allows some structs and enums to be serialized
or deserialized with [serde](https://docs.rs/serde/latest/serde/)

# Description of the Format

Supported time units:

- `seconds`, `second`, `secs`, `sec`
- `minutes`, `minute`, `mins`, `min`
- `hours`, `hour`
- `days`, `day`
- `weeks`, `week`
- `fortnights`, `fortnight` (2 weeks)
- `months`, `month` (defined as `30.44` days or a `1/12` year)
- `years`, `year` (defined as `365.25` days)

The special keywords `yesterday` worth `-1 day`, `tomorrow` worth `+1 day`, `today` and `now` each
worth a zero duration are allowed, too. These keywords count as a full duration and don't accept a
number, time unit or the `ago` time unit suffix.

Summary of the rest of the format:

- Only numbers like `"123 days"` without fraction (like in `"1.2 days"`) and without exponent (like
`"3e9 days"`) are allowed
- Multiple durations like `"1sec 2min"` or `"1week2secs"` in the source string accumulate
- Time units without a number (like in `"second"`) are allowed and a value of `1` is assumed.
- The parsed duration represents the value exactly (without rounding errors as would occur in
floating point calculations) as it is specified in the source string.
- The maximum supported duration (`Duration::MAX`) has `u64::MAX` seconds
(`18_446_744_073_709_551_615`) and `999_999_999` nano seconds
- parsed durations larger than the maximum duration (like `"100000000000000years"`) saturate at
the maximum duration
- Negative durations like `"-1min"` or `"1 week ago"` are allowed
- Any leading, trailing whitespace or whitespace between the number and the time unit (like in `"1
\n sec"`) and multiple durations (like in `"1week \n 2minutes"`) is ignored and follows the posix
definition of whitespace which is:
    - Space (`' '`)
    - Horizontal Tab (`'\x09'`)
    - Line Feed (`'\x0A'`)
    - Vertical Tab (`'\x0B'`)
    - Form Feed (`'\x0C'`)
    - Carriage Return (`'\x0D'`)

Please see also the gnu [documentation] for a description of their format.

# Examples

A re-usable parser

```rust
use fundu::Duration;
use fundu_gnu::RelativeTimeParser;

const PARSER: RelativeTimeParser = RelativeTimeParser::new();

let parser = &PARSER;
assert_eq!(parser.parse("1hour"), Ok(Duration::positive(60 * 60, 0)));
assert_eq!(parser.parse("minute"), Ok(Duration::positive(60, 0)));
assert_eq!(
    parser.parse("2 hours"),
    Ok(Duration::positive(2 * 60 * 60, 0))
);
assert_eq!(parser.parse("second"), Ok(Duration::positive(1, 0)));
assert_eq!(
    parser.parse("1year 12months"),
    Ok(Duration::positive(63_115_200, 0))
);
assert_eq!(parser.parse("-3minutes"), Ok(Duration::negative(3 * 60, 0)));
assert_eq!(
    parser.parse("3 mins ago"),
    Ok(Duration::negative(3 * 60, 0))
);
assert_eq!(
    parser.parse("999sec +1day"),
    Ok(Duration::positive(86_400 + 999, 0))
);
assert_eq!(
    parser.parse("55secs500week"),
    Ok(Duration::positive(55 + 500 * 7 * 24 * 60 * 60, 0))
);
assert_eq!(
    parser.parse("300mins20secs 5hour"),
    Ok(Duration::positive(300 * 60 + 20 + 5 * 60 * 60, 0))
);
assert_eq!(
    parser.parse("123456789"),
    Ok(Duration::positive(123_456_789, 0))
);
assert_eq!(
    parser.parse("42fortnight"),
    Ok(Duration::positive(42 * 2 * 7 * 24 * 60 * 60, 0))
);
assert_eq!(
    parser.parse("yesterday"),
    Ok(Duration::negative(24 * 60 * 60, 0))
);
assert_eq!(parser.parse("now"), Ok(Duration::positive(0, 0)));
assert_eq!(
    parser.parse("today -10seconds"),
    Ok(Duration::negative(10, 0))
);
assert_eq!(
    parser.parse("1000000000000000000000000000000000000years"),
    Ok(Duration::MAX)
);
```

Or use the global method [`parse`]

```rust
use fundu::Duration;
use fundu_gnu::parse;

assert_eq!(parse("123 sec"), Ok(Duration::positive(123, 0)));
assert_eq!(parse("1sec3min"), Ok(Duration::positive(1 + 3 * 60, 0)));
```

# Benchmarks

To run the benchmarks on your machine, clone the repository

```shell
git clone https://github.com/Joining7943/fundu.git
cd fundu
```

and then run the `fundu-gnu` benchmarks with

```shell
cargo bench --package fundu-gnu
```

The above won't run the `flamegraph` and `iai-callgrind` benchmarks.

The `iai-callgrind` (feature = `with-iai`) and `flamegraph` (feature = `with-flamegraph`) benchmarks
can only be run on unix. Use the `--features` option of cargo to run the benchmarks with these
features.

To get a rough idea about the parsing times, here the average parsing speed of some inputs (Quad core 3000Mhz, 8GB DDR3, Linux):

Input | avg parsing time
--- | ---:|
`1` | `67.685 ns`
`123456789` | `72.265 ns`
`"1".repeat(1022)` | `266.01 ns`
`1sec` | `102.45 ns`
`1minutes` | `158.92 ns`
`1sec 1min` | `235.11 ns`
`1sec 1min 1sec 1min` | `476.53 ns`
`1sec 1min 1hour 1day` | `527.04 ns`
`"1sec 1min".repeat(100)` | `22.895 µs`

# TODO

- Gnu allows numerals like `this second`, `next week` etc. (See issue
[#23](https://github.com/Joining7943/fundu/issues/23))
- Gnu treats years and months in the source string as fuzzy. Currently `fundu` only supports static
years and month definitions like `1year = 365.25 days`

# License

MIT license ([LICENSE](LICENSE) or <http://opensource.org/licenses/MIT>)

[`std::time::Duration`]: https://doc.rust-lang.org/std/time/struct.Duration.html
[`chrono::Duration`]: https://docs.rs/chrono/latest/chrono/struct.Duration.html
[`time::Duration`]: https://docs.rs/time/latest/time/struct.Duration.html
[documentation]: https://www.gnu.org/software/coreutils/manual/html_node/Relative-items-in-date-strings.html
