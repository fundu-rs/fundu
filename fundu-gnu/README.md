<!--
 Copyright (c) 2023 Joining7943 <joining@posteo.de>

 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<h1 align="center">Fast and precise gnu relative time parser of rust strings to a Duration</h1>
<div align="center">
    <a href="https://docs.rs/crate/fundu-gnu/">fundu-gnu Docs</a>
    |
    <a href="https://github.com/fundu-rs/fundu/blob/main/CHANGELOG.md">Changelog</a>
</div>
<br>
<div align="center">
    <a href="https://github.com/fundu-rs/fundu/actions">
        <img src="https://github.com/fundu-rs/fundu/actions/workflows/cicd.yml/badge.svg" alt="GitHub branch checks state"/>
    </a>
    <a href="https://codecov.io/gh/fundu-rs/fundu" >
        <img src="https://codecov.io/gh/fundu-rs/fundu/branch/main/graph/badge.svg?token=7GOQ1A6UPH"/>
    </a>
    <a href="https://crates.io/crates/fundu-gnu">
        <img src="https://img.shields.io/crates/v/fundu-gnu.svg" alt="Crates.io"/>
    </a>
    <a href="https://docs.rs/fundu-gnu/">
        <img src="https://docs.rs/fundu-gnu/badge.svg" alt="docs.rs"/>
    </a>
    <a href="https://github.com/rust-lang/rust">
        <img src="https://img.shields.io/badge/MSRV-1.66.0-brightgreen" alt="MSRV"/>
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

This crate provides a simple to use and fast parser based on [fundu](../README.md) aiming for full
compatibility with [gnu](https://www.gnu.org/) relative items in date strings format as specified in
their [documentation].

`fundu-gnu` can parse rust strings with `RelativeTimeParser::parse` and others or the global `parse`
method:

`&str` | Duration |
-- | -- |
`"1hour"`| `Duration::positive(60 * 60, 0)` |
`"minute"`| `Duration::positive(60, 0)` |
`"2 hours"`| `Duration::positive(2 * 60 * 60, 0)` |
`"-3minutes"`| `Duration::negative(3 * 60, 0)` |
`"3 mins ago"`| `Duration::negative(3 * 60, 0)` |
`"999sec +1day"`| `Duration::positive(86_400 + 999, 0)` |
`"55secs500week"`| `Duration::positive(55 + 500 * 604_800, 0)` |
`"123456789"`| `Duration::positive(123_456_789, 0)` |
`"42fortnight"`| `Duration::positive(42 * 2 * 604_800, 0)` |
`"yesterday"`| `Duration::negative(24 * 60 * 60, 0)` |
`"now"`| `Duration::positive(0, 0)` |
`"today -10seconds"`| `Duration::negative(10, 0)` |

`fundu` parses into its own [`Duration`] which is a superset of other `Durations` like
[`std::time::Duration`], [`chrono::Duration`] and [`time::Duration`]. See the
[documentation](https://docs.rs/fundu/latest/fundu/index.html#fundus-duration) how to easily handle
the conversion between these durations. For examples and further documentation see the
[docs](https://docs.rs/fundu-gnu/latest/fundu_gnu/)!

# Audience

This crate is for you if you

- seek a fast and precise gnu compatible duration parser
- want it to simply just work without diving into many customizations
- need to parse a duration relative to a proleptic gregorian date. Since years and months are not
all of equal length in the gregorian calendar, the parsed duration is calculated relative to that
date.
- just like the gnu format
- ...

This crate might not be for you if you want to customize the parser to a format which would not be
compatible with `gnu`. See the main [fundu](../README.md) project, if you want to use a parser
tailored to your needs.

# Installation

Add this to `Cargo.toml`

```toml
[dependencies]
fundu-gnu = "0.3.0"
```

or install with `cargo add fundu-gnu`.

Activating the `chrono` or `time` feature provides a `TryFrom` and `SaturatingInto` implementation
of fundu's `Duration` for [`chrono::Duration`] or [`time::Duration`]. These features also enable a
`From` implementation of [`chrono::DateTime`] or [`time::OffsetDateTime`],
[`time::PrimitiveDateTime`] for fundu-gnu's `DateTime`. Converting from/to [`std::time::Duration`]
does not require an additional feature. Activating the `serde` feature allows some structs and enums
to be serialized or deserialized with [serde](https://docs.rs/serde/latest/serde/)

# Description of the Format

Supported time units:

- `seconds`, `second`, `secs`, `sec`
- `minutes`, `minute`, `mins`, `min`
- `hours`, `hour`
- `days`, `day`
- `weeks`, `week`
- `fortnights`, `fortnight` (2 weeks)
- `months`, `month` (fuzzy)
- `years`, `year` (fuzzy)

Fuzzy time units are not all of equal duration and depend on a given date. If no date is given
when parsing, the system time of `now` in UTC +0 is assumed.

Supported numerals:

- `next` (=1)
- `last` (=-1)
- `this` (=0)
- `first` (=1), `third` (=3), ... , `twelfth` (=12) (Note the missing second which is a time unit)

The special keywords `yesterday` worth `-1 day`, `tomorrow` worth `+1 day`, `today` and `now`
each worth a zero duration are allowed, too. These keywords count as a full duration and don't
accept a number, time unit or the `ago` time unit suffix.

Summary of the rest of the format:

- Time units, keywords (including `ago`) and numerals are case insensitive
- Only numbers like `"123 days"` and without exponent (like `"3e9 days"`) are allowed. Only
seconds time units allow a fraction (like in `"1.123456 secs"`)
- Multiple durations like `"1sec 2min"` or `"1week2secs"` in the source string accumulate
- Time units without a number (like in `"second"`) are allowed and a value of `1` is assumed.
- The parsed duration represents the value exactly (without rounding errors as would occur in
floating point calculations) as it is specified in the source string.
- The maximum supported duration (`Duration::MAX`) has `u64::MAX` seconds
(`18_446_744_073_709_551_615`) and `999_999_999` nano seconds
- parsed durations larger than the maximum duration saturate at the maximum duration
- Negative durations like `"-1min"` or `"1 week ago"` are allowed
- Any leading, trailing whitespace or whitespace between the number and the time unit (like in
`"1 \n sec"`) and multiple durations (like in `"1week \n 2minutes"`) is ignored and follows the
posix definition of whitespace which is:
    - Space (`' '`)
    - Horizontal Tab (`'\x09'`)
    - Line Feed (`'\x0A'`)
    - Vertical Tab (`'\x0B'`)
    - Form Feed (`'\x0C'`)
    - Carriage Return (`'\x0D'`)

Please see also the gnu
[documentation](https://www.gnu.org/software/coreutils/manual/html_node/Relative-items-in-date-strings.html)
for a description of their format.

# Benchmarks

To run the benchmarks on your machine, clone the repository

```shell
git clone https://github.com/fundu-rs/fundu.git
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

To get a rough idea about the parsing times, here the average parsing speed of some inputs (Quad
core 3000Mhz, 8GB DDR3, Linux):

Input | avg parsing time
--- | ---:|
`1` | `49.399 ns`
`123456789` | `57.108 ns`
`"1".repeat(1022)` | `253.89 ns`
`sec` / `1sec` / `seconds` / `1seconds` | `63.521` / `81.871` / `74.962` / `97.785 ns`
`min` / `1min` / `minutes` / `1minutes` | `64.102` / `82.876` / `77.893` / `98.374 ns`
`1year` | `164.30 ns`
`10000000year` | `182.85 ns`
`1sec 1min` | `167.74 ns`
`1sec 1min 1sec 1min` | `325.70 ns`
`1sec 1min 1hour 1day` | `353.18 ns`
`"1sec 1min".repeat(100)` | `15.258 µs`

Parsing of fuzzy time units like in `1year` or `10000000year` adds a considerable amount of
additional computations but is still comparably fast.

# License

MIT license ([LICENSE](LICENSE) or <http://opensource.org/licenses/MIT>)

[`Duration`]: https://docs.rs/fundu-gnu/latest/fundu_gnu/struct.Duration.html
[`std::time::Duration`]: https://doc.rust-lang.org/std/time/struct.Duration.html
[`chrono::Duration`]: https://docs.rs/chrono/latest/chrono/struct.Duration.html
[`time::Duration`]: https://docs.rs/time/latest/time/struct.Duration.html
[`chrono::DateTime`]: https://docs.rs/chrono/latest/chrono/struct.DateTime.html
[`time::PrimitiveDateTime`]: https://docs.rs/time/latest/time/struct.PrimitiveDateTime.html
[`time::OffsetDateTime`]: https://docs.rs/time/latest/time/struct.OffsetDateTime.html
[documentation]: https://www.gnu.org/software/coreutils/manual/html_node/Relative-items-in-date-strings.html
