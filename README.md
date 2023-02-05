<!--
 Copyright (c) 2023 Joining <joining@posteo.de>
 
 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<h1 align="center">Configurable, precise and fast string parser to a rust std::time::Duration</h1>
<div align="center">
    <a href="https://docs.rs/crate/fundu/">Released API Docs</a>
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
    <a href="https://crates.io/crates/fundu">
        <img src="https://img.shields.io/crates/v/fundu.svg" alt="Crates.io"/>
    </a>
    <a href="https://docs.rs/fundu/">
        <img src="https://docs.rs/fundu/badge.svg" alt="docs.rs"/>
    </a>
    <a href="https://github.com/rust-lang/rust">
        <img src="https://img.shields.io/badge/MSRV-1.60.0-brightgreen" alt="MSRV"/>
    </a>
</div>

## Table of Contents

- [Table of Contents](#table-of-contents)
    - [Overview](#overview)
    - [Installation](#installation)
    - [Examples](#examples)
    - [Time Units](#time-units)
    - [Benchmarks](#benchmarks)
    - [Platform support](#platform-support)
    - [Todo](#todo)
    - [License](#license)
  
# Overview

`fundu` provides a parser to parse strings into a [`std::time::Duration`]. It tries to improve on
the standard method `Duration::from_secs_f64(input.parse().unwrap())` ([`Duration::from_secs_f64`])
by

- Providing customizable [TimeUnit](#time-units)s which are accepted in the input string.
- Using no floating point calculations and precisely parse the input as it is. So, what you put
in you is what you get out within the range of a `std::time::Duration`.
- Evaluating to [`Duration::MAX`] if the input number was larger than that maximum or
the input string was positive `infinity`.
- Supporting input strings of arbitrary length.
- Providing better error messages.

This library aims for low runtime costs (See [Benchmarks](#benchmarks)) and being a lightweight
crate. `fundu` is purely built on top of the rust `stdlib`, and there are no additional dependencies
required. The accepted string format is almost the same like the scientific floating point format
and compatible to the [`f64::from_str`] format. In other words, if the accepted input string could
previously converted to an `f64` with `f64::from_str`, no change is needed to accept the same format
with `fundu`. For further details see the [Documentation](https://docs.rs/crate/fundu)!

# Installation

Add this to `Cargo.toml`

```toml
[dependencies]
fundu = "0.2.1"
```

# Examples

If only the default configuration is required, the `parse_duration` method can be used.

```rust
use fundu::parse_duration;
use std::time::Duration;

let input = "1.0e2s";
assert_eq!(parse_duration(input).unwrap(), Duration::new(100, 0));
```

When a customization of the accepted [TimeUnit](#time-units)s is required, then the builder
`DurationParser` can be used.

```rust
use fundu::DurationParser;
use std::time::Duration;

let input = "3m";
assert_eq!(DurationParser::with_all_time_units().parse(input).unwrap(), Duration::new(180, 0));
```

When no time units are configured, seconds is assumed.

```rust
use fundu::DurationParser;
use std::time::Duration;

let input = "1.0e2";
assert_eq!(DurationParser::without_time_units().parse(input).unwrap(), Duration::new(100, 0));
```

However, this will return an error because `y` (Years) is not a default time unit.

```rust
use fundu::DurationParser;

let input = "3y";
assert!(DurationParser::new().parse(input).is_err());
```

The parser is reusable and the set of time units is fully customizable

```rust
use fundu::{DurationParser, TimeUnit::*};
use std::time::Duration;

let mut parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);
for (input, expected) in &[
    ("9e3ns", Duration::new(0, 9000)),
    ("10m", Duration::new(600, 0)),
    ("1.1h", Duration::new(3960, 0)),
    ("7", Duration::new(7, 0)),
] {
    assert_eq!(parser.parse(input).unwrap(), *expected);
}
```

Also, `fundu` tries to give informative error messages

```rust
use fundu::DurationParser;
use std::time::Duration;

assert_eq!(
    DurationParser::without_time_units()
        .parse("1y")
        .unwrap_err()
        .to_string(),
    "Syntax error: No time units allowed but found: y at column 1"
);
```

# Time units

Time units are used to calculate the final `Duration`. `Seconds` are the default unit if no time
unit was present in the input string. The table below gives an overview of the constructor methods
and which time units are available. If a custom set of time units is required,
`DurationParser::with_time_units` can be used.

Name | Time unit | Calculation | `DurationParser::new` \| `parse_duration` | `DurationParser::` `with_all_time_units` | `DurationParser::` `without_time_units`
--- | --- | --- | --- | --- | ---
Nanoseconds | ns | 1e-9s | &#9745; | &#9745; | &#9744;
Microseconds | Ms | 1e-6s | &#9745; | &#9745; | &#9744;
Milliseconds | ms | 1e-3s |&#9745; | &#9745; | &#9744;
Seconds | s | SI definition | &#9745; | &#9745; | &#9744; (seconds is still used as base)
Minutes | m | 60s | &#9745; | &#9745; | &#9744;
Hours | h | 60m | &#9745; | &#9745; | &#9744;
Days | d | 24h | &#9745; | &#9745; | &#9744;
Weeks | w | 7d | &#9745; | &#9745; | &#9744;
Months | M | Year / 12 | &#9744; | &#9745; | &#9744;
Years | y | 365.25d | &#9744; | &#9745; | &#9744;

Note, that `Months` and `Years` are not included in the default configuration. The current
implementation uses an approximate calculation of `Months` and `Years` in seconds. If they are
included in the final configuration, the Julian year based calculation is used. (See table)

# Benchmarks

To run the benchmarks on your machine, clone the repository

```bash
git clone https://github.com/Joining7943/fundu.git
cd fundu
```

and then run the benchmarks with

```bash
cargo bench
```

To get a rough idea about the parsing times, here the average parsing speed of two inputs on a
comparatively slow machine (Quad core 3000Mhz, 8GB DDR3, Linux)

Input | parser with time units | avg parsing time | ~ samples / s
--- | --- | --- | ---
`1` | no | `48.716 ns` | `20_527_136.874`
`1` | yes | `52.548 ns` | `19_030_219.989`
`format!("{}.{}e-1022", "1".repeat(1022), "1".repeat(1022))` | no | `3.7219 µs` | `268_679.975`
`format!("{}.{}e-1022", "1".repeat(1022), "1".repeat(1022))` | yes | `3.7132 µs` | `269_309.490`

# Platform support

Since `fundu` is purely built on top of the rust `stdlib` without platform specific code, this
library should be compatible with all platforms. Please open an issue if you find any unsupported
platforms which `rust` itself supports.

See also the [CI](https://github.com/Joining7943/fundu/actions/workflows/cicd.yml)

# TODO

- Improve api documentation
- Improve performance especially for long inputs
- Make base unit configurable to a different time unit than seconds.
- Implement usage of more than one identifier for time units
- Add more build targets in the CI
- Provide other year calculations:
    - mean Gregorian year
    - Sidereal year
    - Tropical year

See also [Changelog](CHANGELOG.md)

# License

MIT license ([LICENSE](LICENSE) or <http://opensource.org/licenses/MIT>)

[`std::time::Duration`]: https://doc.rust-lang.org/std/time/struct.Duration.html
[`Duration::from_secs_f64`]: https://doc.rust-lang.org/std/time/struct.Duration.html#method.from_secs_f64
[`Duration::MAX`]: https://doc.rust-lang.org/std/time/struct.Duration.html#associatedconstant.MAX
[`f64::from_str`]: https://doc.rust-lang.org/std/primitive.f64.html#impl-FromStr-for-f64
