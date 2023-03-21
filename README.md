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
    - [Comparison](#comparison-fundu-vs-durationtry_from_secs_f64)
    - [Platform support](#platform-support)
    - [Todo](#todo)
    - [License](#license)
  
# Overview

`fundu` provides a parser to convert strings into a [`std::time::Duration`]. It tries to improve on
the standard methods [`Duration::from_secs_f64`] and [`Duration::try_from_secs_f64`] (which is
stable since `1.66.0`) with intermediate parsing to a float via [`f64::from_str`] by

- Merging the separate steps of parsing float like strings to `f64` and parsing of `f64` to a [`Duration`]
- Providing customizable [TimeUnit](#time-units)s which are accepted in the input string.
- Using no floating point calculations and precisely parse the input as it is. So, what you put
in you is what you get out within the range of a `std::time::Duration`.
- Evaluating to [`Duration::MAX`] if the input number was larger than that maximum or
the input string was positive `infinity`.
- Supporting input strings of arbitrary length.
- Providing better error messages.

This library aims for good performance (See [Benchmarks](#benchmarks)) and being a lightweight
crate. `fundu` is purely built on top of the rust `stdlib`, and there are no additional dependencies
required. The accepted string format is almost the same like the scientific floating point format
and compatible to the [`f64::from_str`] format. In other words, if the accepted input string could
previously converted to an `f64` with `f64::from_str`, no change is needed to accept the same format
with `fundu`. For a direct comparison of `fundu` vs the rust native methods
`Duration::(try_)from_secs_f64` see [Comparison](#comparison-fundu-vs-durationtry_from_secs_f64).
For further details see the [Documentation](https://docs.rs/crate/fundu)!

# Installation

Add this to `Cargo.toml` for `fundu` with the `standard` feature.

```toml
[dependencies]
fundu = "0.4.3"
```

fundu is split into two features, `standard` (providing `DurationParser` and `parse_duration`) and
`custom` (providing the `CustomDurationParser`). The first is described here in in detail, the
latter adds fully customizable identifiers for [time units](#time-units). Most of the time only one
of the parsers is needed. To include only the `CustomDurationParser` add the following to
`Cargo.toml`:

```toml
[dependencies]
fundu = { version = "0.4.3", default-features = false, features = ["custom"] }
```

# Examples

If only the default parser is required once, then the `parse_duration` method can be used.

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
assert_eq!(
    DurationParser::with_all_time_units().parse(input).unwrap(),
    Duration::new(180, 0)
);
```

When no time units are configured, seconds is assumed.

```rust
use fundu::DurationParser;
use std::time::Duration;

let input = "1.0e2";
assert_eq!(
    DurationParser::without_time_units().parse(input).unwrap(),
    Duration::new(100, 0)
);
```

However, setting the default time unit to something different than seconds can be achieved with

```rust
use fundu::{DurationParser, TimeUnit::*};
use std::time::Duration;

assert_eq!(
    DurationParser::without_time_units().default_unit(MilliSecond).parse("1000").unwrap(),
    Duration::new(1, 0)
);
```

Note the following will return an error because `y` (Years) is not in the default set of
[TimeUnits](#time-units).

```rust
use fundu::DurationParser;

let input = "3y";
assert!(DurationParser::new().parse(input).is_err());
```

The parser is reusable and the set of time units is fully customizable

```rust
use fundu::{DurationParser, TimeUnit::*};
use std::time::Duration;

let parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);
for (input, expected) in &[
    ("9e3ns", Duration::new(0, 9000)),
    ("10m", Duration::new(600, 0)),
    ("1.1h", Duration::new(3960, 0)),
    ("7", Duration::new(7, 0)),
] {
    assert_eq!(parser.parse(input).unwrap(), *expected);
}
```

The identifiers for time units can be fully customized with any number of valid
[utf-8](https://en.wikipedia.org/wiki/UTF-8) sequences if the `custom` feature is activated:

```rust
use fundu::{CustomDurationParser, TimeUnit::*};
use std::time::Duration;

let parser = CustomDurationParser::with_time_units(
    &[
        (MilliSecond, &["χιλιοστό του δευτερολέπτου"]),
        (Second, &["s", "secs", "..."]),
        (Hour, &["⏳"])
    ]
);
for (input, expected) in &[
    (".3χιλιοστό του δευτερολέπτου", Duration::new(0, 300_000)),
    ("1e3...", Duration::new(1000, 0)),
    ("1.1⏳", Duration::new(3960, 0)),
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
    "Time unit error: No time units allowed but found: 'y' at column 1"
);
```

See also the [examples folder](examples) for common recipes. Run an example with

```shell
cargo run --example $FILE_NAME_WITHOUT_FILETYPE_SUFFIX
```

# Time units

Time units are used to calculate the final `Duration`. `Second` is the default time unit (if not
specified otherwise) and if no time unit was specified in the input string. The table below gives an
overview of the constructor methods and which time units are available. If a custom set of time
units is required, `DurationParser::with_time_units` can be used.

Name | Time unit | Calculation | `DurationParser::new` \| `parse_duration` | `DurationParser::` `with_all_time_units` | `DurationParser::` `without_time_units`
--- | --- | --- | --- | --- | ---
`Nanoseconds` | ns | `1e-9s` | &#9745; | &#9745; | &#9744;
`Microseconds` | Ms | `1e-6s` | &#9745; | &#9745; | &#9744;
`Milliseconds` | ms | `1e-3s` |&#9745; | &#9745; | &#9744;
`Seconds` | s | SI definition | &#9745; | &#9745; | &#9744;
`Minutes` | m | `60s` | &#9745; | &#9745; | &#9744;
`Hours` | h | `60m` | &#9745; | &#9745; | &#9744;
`Days` | d | `24h` | &#9745; | &#9745; | &#9744;
`Weeks` | w | `7d` | &#9745; | &#9745; | &#9744;
`Months` | M | `Year / 12` | &#9744; | &#9745; | &#9744;
`Years` | y | `365.25d` | &#9744; | &#9745; | &#9744;

Note that `Months` and `Years` are not included in the default set of time units. The current
implementation uses an approximate calculation of `Months` and `Years` in seconds and if they are
included in the final configuration, the [Julian
year](https://en.wikipedia.org/wiki/Julian_year_(astronomy)) based calculation is used. (See table
above)

With the `CustomDurationParser` in the `custom` feature, the identifiers for time units can be fully
customized.

# Benchmarks

To run the benchmarks on your machine, clone the repository

```shell
git clone https://github.com/Joining7943/fundu.git
cd fundu
```

and then run all benchmarks with

```shell
cargo bench --all-features
```

Benchmarks can be filtered for example with

```shell
cargo bench --bench benchmarks_standard
cargo bench --bench benchmarks_standard -- 'parsing speed'
cargo bench --features custom --no-default-features --bench benchmarks_custom
```

For more infos, see the help with

```shell
cargo bench --help # The cargo help for bench
cargo bench --bench benchmarks_standard -- --help # The criterion help
```

To get a rough idea about the parsing times, here the average parsing speed of two inputs on a
comparatively slow machine (Quad core 3000Mhz, 8GB DDR3, Linux)

Input | parser with time units | avg parsing time | ~ samples / s
--- | --- | --- | ---
`1` | no | `39.879 ns` | `25_075_854.459`
`1` | yes | `41.199 ns` | `24_272_433.796`
`format!("{}.{}e-1022", "1".repeat(1022), "1".repeat(1022))` | no | `589.50 ns` | `1_696_352.841`
`format!("{}.{}e-1022", "1".repeat(1022), "1".repeat(1022))` | yes | `590.68 ns` | `1_692_964.041`

For comparison, `fundu`'s precision and additional features only add a very low performance overhead
for small input and outperforms the reference function for larger input (the reference function is
`Duration::from_secs_f64(input.parse().unwrap())`):

Input | avg parsing time | ~ samples / s
--- | --- | ---
`1` | `25.630 ns` | `39_016_777.214`
`format!("{}.{}e-1022", "1".repeat(1022), "1".repeat(1022))` | `1.7457 µs` | `572_836.111`

# Comparison `fundu` vs `Duration::(try_)from_secs_f64`

Here's a short incomplete overview of differences and advantages of `fundu` over using
`Duration::(try_)from_secs_f64(input.parse().unwrap())`

Input | Result `fundu` | Result `Duration::(try_)from_secs_f64`
--- | --- | ---
`01271480964981728917.1` | `Duration::new(1_271_480_964_981_728_917, 100_000_000)` | `Duration::new(1_271_480_964_981_729_024, 0)`
`1.11111111111e10` | `Duration::new(11_111_111_111, 100_000_000)` | `Duration::new(11_111_111_111, 100_000_381)`
`1ns` | `Duration::new(0, 1)` | cannot parse time units
`1000` | When changing the default unit to `MilliSecond` -> `Duration::new(1, 0)` | is always seconds based
`1e20` | `Duration::MAX` | panics or returns an error due to: `can not convert float seconds to Duration: value is either too big or NaN`
`infinity` | `DURATION::MAX` | panics or returns an error due to: `can not convert float seconds to Duration: value is either too big or NaN`

`fundu` has a small impact on performance when the input is small but performs better for large
input (See [performance](#benchmarks)). Depending on the input data and if you need to parse a
massive amount of inputs and don't need the full precision or any of `fundu`'s features, you may
prefer using the native methods from the rust `stdlib`.

# Platform support

Since `fundu` is purely built on top of the rust `stdlib` without platform specific code, this
library should be compatible with all platforms. Please open an issue if you find any unsupported
platforms which `rust` itself supports.

See also the [CI](https://github.com/Joining7943/fundu/actions/workflows/cicd.yml)

# TODO

- Provide other year calculations:
    - mean Gregorian year
    - Sidereal year
    - Tropical year

See also [Changelog](CHANGELOG.md)

# License

MIT license ([LICENSE](LICENSE) or <http://opensource.org/licenses/MIT>)

[`std::time::Duration`]: https://doc.rust-lang.org/std/time/struct.Duration.html
[`Duration`]: https://doc.rust-lang.org/std/time/struct.Duration.html
[`Duration::from_secs_f64`]: https://doc.rust-lang.org/std/time/struct.Duration.html#method.from_secs_f64
[`Duration::try_from_secs_f64`]: https://doc.rust-lang.org/std/time/struct.Duration.html#method.try_from_secs_f64
[`Duration::MAX`]: https://doc.rust-lang.org/std/time/struct.Duration.html#associatedconstant.MAX
[`f64::from_str`]: https://doc.rust-lang.org/std/primitive.f64.html#impl-FromStr-for-f64
