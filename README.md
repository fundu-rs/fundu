<!--
 Copyright (c) 2023 Joining <joining@posteo.de>
 
 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<h1 align="center">Configurable, precise and fast string parser to a rust std::time::Duration</h1>
<div align="center">
    <a href="https://docs.rs/crate/fundu/">Released API Docs</a>
    |
    <a href="https://github.com/Joining7943/fundu/blob/master/CHANGELOG.md">Changelog</a>
</div>
<br>
<div align="center">
    <a href="https://github.com/Joining7943/fundu/actions">
        <img src="https://github.com/Joining7943/fundu/actions/workflows/cicd.yml/badge.svg" alt="GitHub branch checks state">
    </a>
    <a href="https://crates.io/crates/fundu">
        <img src="https://img.shields.io/crates/v/fundu.svg" alt="Crates.io">
    </a>
    <a href="https://docs.rs/fundu/">
        <img src="https://docs.rs/fundu/badge.svg" alt="docs.rs">
    </a>
    <a href="https://github.com/rust-lang/rust">
        <img src="https://img.shields.io/badge/MSRV-1.60.0-brightgreen" alt="docs.rs">
    </a>
</div>

## Table of Contents

- [Table of Contents](#table-of-contents)
    - [Overview](#overview)
    - [Installation](#installation)
    - [Examples](#examples)
    - [Time Units](#time-units)
    - [Benchmarks](#benchmarks)
    - [Todo](#todo)
    - [License](#license)
  
## Overview

`fundu` provides a duration parser to parse strings into a [std::time::Duration](https://doc.rust-lang.org/std/time/struct.Duration.html). It tries to improve on the standard method `Duration::from_secs_f64(input.parse().unwrap())` by

- Providing customizable [TimeUnit](#time-units)s which are accepted in the input string.
- Using no floating point calculations and precisely parse the input as it is. So, what you put
in you is what you get out within the range of a `std::time::Duration`.
- Evaluating to [std::time::Duration::MAX](https://doc.rust-lang.org/std/time/struct.Duration.html#associatedconstant.MAX) if the input number was larger than that maximum or
the input string was positive `infinity`
- Providing better error messages in case of parsing errors.

These features come with low additional runtime costs by still being a lightweight crate.
This crate is built on top of the rust `stdlib`, and no additional dependencies are required. The
accepted number format is almost the same like the scientific floating point format by being compatible to the [f64 format](https://doc.rust-lang.org/std/primitive.f64.html#impl-FromStr-for-f64). In other words, if the accepted format was `f64` before there is no change needed to accept the same format with `fundu`. For further details
see the [Documentation](https://docs.rs/fundu)!

# Installation

```toml
[dependencies]
fundu = "0.1.0"
```

# Examples

If only the default configuration is required the `parse_duration` method can be used.

```rust
use fundu::parse_duration;
use std::time::Duration;

let input = "1.0e2s";
assert_eq!(parse_duration(input).unwrap(), Duration::new(100, 0));
```

When a customization of the accepted [TimeUnit](#time-units)s is required then the builder
`DurationParser` can be used.

```rust
use fundu::DurationParser;
use std::time::Duration;

let input = "3m";
assert_eq!(DurationParser::with_all_time_units().parse(input).unwrap(), Duration::new(180, 0));
```

With no time units allowed always seconds is assumed.

```rust
use fundu::DurationParser;
use std::time::Duration;

let input = "1.0e2";
assert_eq!(DurationParser::with_no_time_units().parse(input).unwrap(), Duration::new(100, 0));
```

This will return an error because `y` (years) is not a default time unit.

```rust
use fundu::DurationParser;

let input = "3y";
assert!(DurationParser::new().parse(input).is_err());
```

# Time units

Time units are used to calculate the final `Duration`. `Seconds` are the base unit if no time unit was found in the input string. Below is an overview of the standard constructor methods. If any other time units configuration is required there is `DurationParser::with_time_units` to provide a custom configuration.

Name | Accepted Time unit | `DurationParser::new` \| `parse_duration` | `DurationParser::` `with_all_time_units` | `DurationParser::` `with_no_time_units`
--- | --- | --- | --- | ---
Nanoseconds | ns | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Microseconds | Ms | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Milliseconds | ms | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Seconds (base unit if no time unit was present) | s | :heavy_check_mark: | :heavy_check_mark: | :white_large_square: (seconds is still used as base)
Minutes | m | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Hours | h | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Days | d | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Weeks | w | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Months | M | :white_large_square: | :heavy_check_mark: | :white_large_square:
Years | y | :white_large_square: | :heavy_check_mark: | :white_large_square:

Note, that `Months` and `Years` are not included in the default configuration. This is due to the lack of a precise and common definition of `Months` and `Years` in seconds. If they are included in the final configuration then currently only the common gregorian calendar based calculation is available:

1 year = 365 days and 1 Month = 30 days.

# Benchmarks

Clone the repository

```bash
git clone https://github.com/Joining7943/fundu
cd fundu
```

and then run the benchmarks

```bash
cargo bench
```

# TODO

See [Changelog](../Changelog.md)

# License

MIT license ([LICENSE](../LICENSE) or <http://opensource.org/licenses/MIT>)
