<!--
 Copyright (c) 2023 Joining7943 <joining@posteo.de>

 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<h1 align="center">Fast and precise systemd time span parser of rust strings to a Duration</h1>
<div align="center">
    <a href="https://docs.rs/crate/fundu-systemd/">fundu-systemd Docs</a>
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
    <a href="https://crates.io/crates/fundu-systemd">
        <img src="https://img.shields.io/crates/v/fundu-systemd.svg" alt="Crates.io"/>
    </a>
    <a href="https://docs.rs/fundu-systemd/">
        <img src="https://docs.rs/fundu-systemd/badge.svg" alt="docs.rs"/>
    </a>
    <a href="https://github.com/rust-lang/rust">
        <img src="https://img.shields.io/badge/MSRV-1.74.1-brightgreen" alt="MSRV"/>
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
the [systemd](https://www.freedesktop.org/wiki/Software/systemd/) time span format as specified in
their [documentation](https://www.freedesktop.org/software/systemd/man/systemd.time.html).

`fundu-systemd` can parse rust strings like

| `&str` | Duration |
| -- | -- |
| `"2 h"` | `Duration::positive(2 * 60 * 60, 0)` |
| `"2hours"` |`Duration::positive(2 * 60 * 60, 0)` |
| `"second"` |`Duration::positive(1, 0)` |
| `"48hr"` |`Duration::positive(48 * 60 * 60, 0)` |
| `"12.3 seconds"` |`Duration::positive(12, 300_000_000)` |
| `"1y 12month"` | `Duration::positive(63_115_200, 0)` |
| `"999us +1d"` |`Duration::positive(86_400, 999_000)` |
| `"55s500ms"` | `Duration::positive(55, 500_000_000)` |
| `"300ms20s 5day"` |`Duration::positive(20 + 5 * 60 * 60 * 24, 300_000_000)` |
| `"123456789"` |`Duration::positive(123_456_789, 0)` (Default: Second) |
| `"100"` |`Duration::positive(0, 100_000)` (when default is set to MicroSecond) |
| `"infinity"` | variable: the maximum duration which is currently in use (see below) |

Note that `fundu` parses into its own `Duration` which is a superset of other `Durations` like
[`std::time::Duration`], [`chrono::Duration`] and [`time::Duration`]. See the
[documentation](https://docs.rs/fundu/latest/fundu/index.html#fundus-duration) how to easily
handle the conversion between these durations.

# Audience

This crate is for you if you

- seek a fast and reliable systemd compatible duration parser
- want it to simply just work without diving into many customizations
- just like the systemd format
- ...

This crate might not be for you if you want to customize the parser to a format which would not be
compatible with `systemd`. See the main [fundu](../README.md) project, if you want to use a parser
tailored to your needs.

# Installation

Add this to `Cargo.toml`

```toml
[dependencies]
fundu-systemd = "0.3.1"
```

or install with `cargo add fundu-systemd`.

Activating the `chrono` or `time` feature provides a `TryFrom` implementation for
[`chrono::Duration`] or [`time::Duration`]. Converting from/to [`std::time::Duration`] does not require
an additional feature. Activating the `serde` feature allows some structs and enums to be serialized
or deserialized with [serde](https://docs.rs/serde/latest/serde/)

# Description of the Format

Supported time units:

- `nsec`, `ns` (can be switched on, per default these are not included)
- `usec`, `us`, `µs`
- `msec,` `ms`
- `seconds`, `second`, `sec`, `s`
- `minutes`, `minute`, `min`, `m`
- `hours`, `hour`, `hr`, `h`
- `days`, `day`, `d`
- `weeks`, `week`, `w`
- `months`, `month`, `M` (defined as `30.44` days or a `1/12` year)
- `years`, `year`, `y` (defined as `365.25` days)

Summary of the rest of the format:

- Only numbers like `"123 days"` or with fraction `"1.2 days"` but without exponent (like `"3e9
days"`) are allowed
- For numbers without a time unit (like `"1234"`) the default time unit is usually `second` but can
be changed since in some case systemd uses a different granularity.
- Time units without a number (like in `"second"`) are allowed and a value of `1` is assumed.
- The parsed duration represents the value exactly (without rounding errors as would occur in
floating point calculations) as it is specified in the source string (just like systemd).
- The maximum supported duration (`Duration::MAX`) has `u64::MAX` seconds
(`18_446_744_073_709_551_615`) and `999_999_999` nano seconds. However, systemd uses `u64::MAX`
micro seconds as maximum duration when parsing without nanos and `u64::MAX` nano seconds when
parsing with nanos. `fundu-systemd` provides the `parse` and `parse_nanos` functions to reflect
that. If you don't like the maximum duration of `systemd` it's still possible via `parse_with_max`
and `parse_nanos_with_max` to adjust this limit to a duration ranging from `Duration::ZERO` to
`Duration::MAX`.
- The special value `"infinity"` evaluates to the maximum duration. Note the maximum duration
depends on whether parsing with nano seconds or without. If the maximum duration is manually set to
a different value then it evaluates to that maximum duration.
- parsed durations larger than the maximum duration (like `"100000000000000years"`)
saturate at the maximum duration
- Negative durations are not allowed, also no intermediate negative durations like in `"5day -1ms"`
although the final duration would not be negative.
- Any leading, trailing whitespace or whitespace between the number and the time unit (like in `"1
\n sec"`) and multiple durations (like in `"1week \n 2minutes"`) is ignored and follows the posix
definition of whitespace which is:
    - Space (`' '`)
    - Horizontal Tab (`'\x09'`)
    - Line Feed (`'\x0A'`)
    - Vertical Tab (`'\x0B'`)
    - Form Feed (`'\x0C'`)
    - Carriage Return (`'\x0D'`)

Please see also the systemd
[documentation](https://www.freedesktop.org/software/systemd/man/systemd.time.html) for a
description of their format.

# Benchmarks

To run the benchmarks on your machine, clone the repository

```shell
git clone https://github.com/fundu-rs/fundu.git
cd fundu
```

and then run the `fundu-systemd` benchmarks with

```shell
cargo bench --package fundu-systemd
```

The above won't run the `flamegraph` and `iai-callgrind` benchmarks.

The `iai-callgrind` (feature = `with-iai`) and `flamegraph` (feature = `with-flamegraph`) benchmarks
can only be run on unix. Use the `--features` option of cargo to run the benchmarks with these
features.

To get a rough idea about the parsing times, here the average parsing speed of some inputs (Quad core 3000Mhz, 8GB DDR3, Linux):

Input | avg parsing time
--- | ---:|
`1` | `55.572 ns`
`123456789.123456789` | `88.750 ns`
`format!("{}.{}", "1".repeat(1022), "1".repeat(1022))` | `475.07 ns`
`s` | `83.724 ns`
`minutes` | `133.26 ns`
`1ns 1us` | `200.59 ns`
`1ns 1us 1ms 1s` | `379.75 ns`
`1ns 1us 1ns 1us` | `391.54 ns`
`"1ns 1us".repeat(100)` | `18.644 µs`

# License

MIT license ([LICENSE](LICENSE) or <http://opensource.org/licenses/MIT>)

[`std::time::Duration`]: https://doc.rust-lang.org/std/time/struct.Duration.html
[`chrono::Duration`]: https://docs.rs/chrono/latest/chrono/struct.Duration.html
[`time::Duration`]: https://docs.rs/time/latest/time/struct.Duration.html
