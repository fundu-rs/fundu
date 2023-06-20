<!--
 Copyright (c) 2023 Joining7943 <joining@posteo.de>

 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<h1 align="center">Fast and precise systemd time span parser of rust strings to a Duration</h1>
<div align="center">
    <a href="https://docs.rs/crate/fundu-systemd/">fundu-systemd Docs</a>
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
    <a href="https://crates.io/crates/fundu-systemd">
        <img src="https://img.shields.io/crates/v/fundu-systemd.svg" alt="Crates.io"/>
    </a>
    <a href="https://docs.rs/fundu-systemd/">
        <img src="https://docs.rs/fundu-systemd/badge.svg" alt="docs.rs"/>
    </a>
    <a href="https://github.com/rust-lang/rust">
        <img src="https://img.shields.io/badge/MSRV-1.64.0-brightgreen" alt="MSRV"/>
    </a>
</div>

# Overview

This crate provides a simple to use and blazingly fast parser based on [fundu](../README.md) aiming for full compatibility with
the [systemd](https://www.freedesktop.org/wiki/Software/systemd/) time span format as specified in
their [documentation](https://www.freedesktop.org/software/systemd/man/systemd.time.html).

`fundu-systemd` can parse rust strings like

| `&str` | Duration |
| -- | -- |
| `"2 h"` | `Duration::positive(2 * 60 * 60, 0)` |
| `"2hours"` |`Duration::positive(2 * 60 * 60, 0)` |
| `"second"` |`Duration::positive(1, 0)` |
| `"48hr"` |`Duration::positive(48 * 60 * 60, 0)` |
| `"1y 12month"` | `Duration::positive(63_115_200, 0)` |
| `"999us +1d"` |`Duration::positive(86_400, 999_000)` |
| `"55s500ms"` | `Duration::positive(55, 500_000_000)` |
| `"300ms20s 5day"` |`Duration::positive(20 + 5 * 60 * 60 * 24, 300_000_000)` |
| `"123456789"` |`Duration::positive(123_456_789, 0)` |
| `"infinity"` |`Duration::positive(u64::MAX, 999_999_999)` |

Note that `fundu` parses into its own `Duration` which is a superset of other `Durations` like
[`std::time::Duration`], [`chrono::Duration`] and [`time::Duration`]. See the
[documentation](https://docs.rs/fundu/latest/fundu/index.html#fundus-duration) how to easily
handle the conversion between these durations.

# Audience

This crate is for you if you

- seek a fast and reliable systemd compatible duration parser
- want it to simply just work without diving into customizations
- just like the systemd format
- ...

This crate is not for you if you want to customize the parser to a format which would not be
compatible with `systemd`. See the main [fundu](../README.md) project, if you want to use a parser
tailored to your needs.

# Installation

Add this to `Cargo.toml`

```toml
[dependencies]
fundu-systemd = "0.1.0"
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

A summary of the rest of the format:

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
- The special value `"infinity"` evaluates to the maximum systemd duration. Note the maximum
duration depends on whether parsing with nano seconds or without.
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

# Known issues

## Maximum duration

### Issue

The maximum duration sometimes is `i64::MAX` (`9223372036854775807`) micro seconds and sometimes
`u64::MAX` (`18446744073709551615`) micro seconds depending on the time units in the input string.
This looks like a bug in systemd. For example:

- `systemd-analyze timespan infinity` returns `u64::MAX` micro seconds,
- `systemd-analyze timespan 18446744073709551615 usec` returns an error
- `systemd-analyze timespan 9223372036854775807 usec` is valid
- `systemd-analyze timespan 9223372036854775808 usec` returns an error
- `systemd-analyze timespan 584541 years` returns `18446711061600000000` micro seconds which is larger than `i64::MAX`

`fundu-systemd` doesn't make these differences and saturates at the maximum duration of `u64::MAX`
micro seconds (or `u64::MAX` nano seconds if parsing with `parse_nanos`) no matter the time unit in
the input string.

### Mitigation

The maximum duration of fundu-systemd's parser is adjustable to a lower value than `u64::MAX` micro seconds or nano seconds, if needed.

# License

MIT license ([LICENSE](LICENSE) or <http://opensource.org/licenses/MIT>)

[`std::time::Duration`]: https://doc.rust-lang.org/std/time/struct.Duration.html
[`chrono::Duration`]: https://docs.rs/chrono/0.4.24/chrono/struct.Duration.html
[`time::Duration`]: https://docs.rs/time/latest/time/struct.Duration.html
