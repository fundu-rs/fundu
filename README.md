<!--
 Copyright (c) 2023 Joining <joining@posteo.de>
 
 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<h1 align="center">Configurable, precise and fast rust string parser to a Duration</h1>
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
        <img src="https://img.shields.io/badge/MSRV-1.64.0-brightgreen" alt="MSRV"/>
    </a>
</div>

## Table of Contents

- [Table of Contents](#table-of-contents)
    - [Overview](#overview)
    - [Installation](#installation)
    - [Examples](#examples)
    - [Time Units](#time-units)
    - [Customization](#customization)
    - [Benchmarks](#benchmarks)
    - [Comparison](#comparison-fundu-vs-durationfrom_secs_f64)
    - [Platform support](#platform-support)
    - [License](#license)
  
# Overview

`fundu` provides a flexible and fast parser to convert rust strings into a `Duration`. `fundu` parses into
its own `Duration` but provides methods to convert into [`std::time::Duration`],
[`chrono::Duration`] and [`time::Duration`]. Some examples for valid input strings with the
`standard` feature:

- `"1.41"`
- `"42"`
- `"2e-8"`, `"2e+8"` (or likewise `"2.0e8"`)
- `".5"` or likewise `"0.5"`
- `"3."` or likewise `"3.0"`
- `"inf"`, `"+inf"`, `"infinity"`, `"+infinity"`
- `"1w"` (1 week) or likewise `"7d"`, `"168h"`, `"10080m"`, `"604800s"`, ...

For examples of the `custom` feature see [Customization section](#customization).
Summary of features provided by this crate:

- __Precision__: There are no floating point calculations and the input is precisely parsed as it
is. So, what you put in you is what you get out within the range of a `Duration`. (See also
[Comparison](#comparison-fundu-vs-durationfrom_secs_f64))
- __Performance__: The parser is blazingly fast ([Benchmarks](#benchmarks))
- __Customization__: [`TimeUnits`](#time-units), the number format and other aspects are
easily configurable ([Customization](#customization))
- __Sound limits__: The duration saturates at [`Duration::MAX`] if the input number was larger than
that maximum or if the input string was positive `infinity`.
- __Negative Durations__: The parser can be configured to parse negative durations. Fundu's
`Duration` can represent negative durations but also implements `TryFrom` for [`chrono::Duration`]
and [`time::Duration`] if the corresponding feature is activated.
- __Error handling__: The error messages try to be informative on their own but can also be
easily adjusted (See also [Examples](#examples))

`fundu` aims for good performance and being a lightweight crate. It is purely built on top of the
rust `stdlib`, and there are no additional dependencies required in the standard configuration. The
accepted number format is per default the scientific floating point format and compatible with
[`f64::from_str`]. However, the number format and other aspects can be [customized](#customization)
up to formats like [systemd time
spans](https://www.man7.org/linux/man-pages/man7/systemd.time.7.html) or [gnu relative times](https://www.gnu.org/software/coreutils/manual/html_node/Relative-items-in-date-strings.html). See also the examples
[Examples section](#examples) and the [examples](examples) folder. For a direct comparison of
`fundu` vs the rust native methods `Duration::(try_)from_secs_f64` see
[Comparison](#comparison-fundu-vs-durationfrom_secs_f64).

For further details see the [Documentation](https://docs.rs/crate/fundu)!

# Notice

This project currently (after the release of `1.0.0`) undergoes a bigger internal restructuring and
this README might not be up-to-date. Especially, this README describes the main `fundu` package.

# Installation

Add this to `Cargo.toml` for `fundu` with the `standard` feature.

```toml
[dependencies]
fundu = "1.0.0"
```

fundu is split into two main features, `standard` (providing `DurationParser` and `parse_duration`)
and `custom` (providing the `CustomDurationParser`). The first is described here in in detail, the
latter adds fully customizable identifiers for [time units](#time-units). Most of the time only one
of the parsers is needed. To include only the `CustomDurationParser` add the following to
`Cargo.toml`:

```toml
[dependencies]
fundu = { version = "1.0.0", default-features = false, features = ["custom"] }
```

Activating the `chrono` or `time` feature provides a `TryFrom` implementation for [`chrono::Duration`] or [`time::Duration`].

Activating the `serde` feature allows some structs and enums to be serialized or deserialized with [serde](https://docs.rs/serde/latest/serde/)

# Examples

If only the default configuration is required once, the `parse_duration` method can be used.
Note that `parse_duration` returns a [`std::time::Duration`] in contrast to the `parse` method of the other parsers which return a `fundu::Duration`.

```rust
use std::time::Duration;

use fundu::parse_duration;

let input = "1.0e2s";
assert_eq!(parse_duration(input).unwrap(), Duration::new(100, 0));
```

When a customization of the accepted [TimeUnit](#time-units)s is required, then
`DurationParser::with_time_units` can be used.

```rust
use fundu::{Duration, DurationParser};

let input = "3m";
assert_eq!(
    DurationParser::with_all_time_units().parse(input).unwrap(),
    Duration::positive(180, 0)
);
```

When no time units are configured, seconds is assumed.

```rust
use fundu::{Duration, DurationParser};

let input = "1.0e2";
assert_eq!(
    DurationParser::without_time_units().parse(input).unwrap(),
    Duration::positive(100, 0)
);
```

However, the following will return an error because `y` (Years) is not a default time unit:

```rust
use fundu::DurationParser;

let input = "3y";
assert!(DurationParser::new().parse(input).is_err());
```

The parser is reusable and the set of time units is fully customizable

```rust
use fundu::TimeUnit::*;
use fundu::{Duration, DurationParser};

let parser = DurationParser::with_time_units(&[NanoSecond, Minute, Hour]);

assert_eq!(parser.parse("9e3ns").unwrap(), Duration::positive(0, 9000));
assert_eq!(parser.parse("10m").unwrap(), Duration::positive(600, 0));
assert_eq!(parser.parse("1.1h").unwrap(), Duration::positive(3960, 0));
assert_eq!(parser.parse("7").unwrap(), Duration::positive(7, 0));
```

Setting the default time unit (if no time unit is given in the input string) to something
different than seconds is also easily possible

```rust
use fundu::TimeUnit::*;
use fundu::{Duration, DurationParser};

assert_eq!(
    DurationParser::without_time_units()
        .default_unit(MilliSecond)
        .parse("1000")
        .unwrap(),
    Duration::positive(1, 0)
);
```

The identifiers for time units can be fully customized with any number of valid
[utf-8](https://en.wikipedia.org/wiki/UTF-8) sequences if the `custom` feature is activated:

```rust
use fundu::TimeUnit::*;
use fundu::{CustomTimeUnit, CustomDurationParser, Duration};

let parser = CustomDurationParser::with_time_units(&[
    CustomTimeUnit::with_default(MilliSecond, &["χιλιοστό του δευτερολέπτου"]),
    CustomTimeUnit::with_default(Second, &["s", "secs"]),
    CustomTimeUnit::with_default(Hour, &["⏳"]),
]);

assert_eq!(parser.parse(".3χιλιοστό του δευτερολέπτου"), Ok(Duration::positive(0, 300_000)));
assert_eq!(parser.parse("1e3secs"), Ok(Duration::positive(1000, 0)));
assert_eq!(parser.parse("1.1⏳"), Ok(Duration::positive(3960, 0)));
```

The `custom` feature can be used to customize a lot more. See the documentation of the exported
items of the `custom` feature (like `CustomTimeUnit`, `TimeKeyword`) for more information.

Also, `fundu` tries to give informative error messages

```rust
use fundu::DurationParser;

assert_eq!(
    DurationParser::without_time_units()
        .parse("1y")
        .unwrap_err()
        .to_string(),
    "Time unit error: No time units allowed but found: 'y' at column 1"
);
```

The number format can be easily adjusted to your needs. For example to allow numbers being optional,
allow some ascii whitespace between the number and the time unit and restrict the number format to
whole numbers, without fractional part and an exponent (Also note that the `DurationParserBuilder` can
build a `DurationParser` at compile time in `const` context):

```rust
use fundu::TimeUnit::*;
use fundu::{Duration, DurationParser, ParseError};

const PARSER: DurationParser = DurationParser::builder()
    .time_units(&[NanoSecond])
    .allow_delimiter(|byte| matches!(byte, b'\t' | b'\n' | b'\r' | b' '))
    .number_is_optional()
    .disable_fraction()
    .disable_exponent()
    .build();

assert_eq!(PARSER.parse("ns").unwrap(), Duration::positive(0, 1));
assert_eq!(
    PARSER.parse("1000\t\n\r ns").unwrap(),
    Duration::positive(0, 1000)
);

assert_eq!(
    PARSER.parse("1.0ns").unwrap_err(),
    ParseError::Syntax(1, "No fraction allowed".to_string())
);
assert_eq!(
    PARSER.parse("1e9ns").unwrap_err(),
    ParseError::Syntax(1, "No exponent allowed".to_string())
);
```

It's also possible to parse multiple durations at once with `parse_multiple`. The different
durations can be separated by an optional `delimiter` (a closure matching a `u8`) defined with
`parse_multiple`. If the delimiter is not encountered, a number can also indicate a new duration.

```rust
use fundu::{Duration, DurationParser};

let parser = DurationParser::builder()
    .default_time_units()
    .parse_multiple(|byte| matches!(byte, b' ' | b'\t'), Some(&["and"]))
    .build();

assert_eq!(
    parser.parse("1.5h 2e+2ns"),
    Ok(Duration::positive(5400, 200))
);
assert_eq!(
    parser.parse("55s500ms"),
    Ok(Duration::positive(55, 500_000_000))
);
assert_eq!(parser.parse("1\t1"), Ok(Duration::positive(2, 0)));
assert_eq!(
    parser.parse("1.   .1"),
    Ok(Duration::positive(1, 100_000_000))
);
assert_eq!(parser.parse("2h"), Ok(Duration::positive(2 * 60 * 60, 0)));
assert_eq!(
    parser.parse("300ms20s 5d"),
    Ok(Duration::positive(5 * 60 * 60 * 24 + 20, 300_000_000))
);
assert_eq!(
    parser.parse("300.0ms and 5d"),
    Ok(Duration::positive(5 * 60 * 60 * 24, 300_000_000))
);
```

See also the [examples folder](examples) for common recipes and integration with other crates. Run
an example with

```shell
cargo run --example $FILE_NAME_WITHOUT_FILETYPE_SUFFIX
```

like the systemd time span parser example

```shell
# For some of the examples a help is available. To pass arguments to the example itself separate 
# the arguments for cargo and the example with `--`
$ cargo run --example systemd --features custom --no-default-features -- --help
...

# To actually run the example execute
$ cargo run --example systemd --features custom --no-default-features '300ms20s 5day'
Original: 300ms20s 5day
      μs: 432020300000
   Human: 5d 20s 300ms
```

# Time units

`Second` is the default time unit (if not specified otherwise for example with
[`DurationParser::default_unit`]) which is applied when no time unit was encountered in the input
string. The table below gives an overview of the constructor methods and which time units are
available. If a custom set of time units is required, `DurationParser::with_time_units` can be used.

TimeUnit | Default identifier | Calculation | Default time unit
---:| ---:| ---:|:---:
`Nanosecond` | ns | `1e-9s` | &#9745;
`Microsecond` | Ms | `1e-6s` | &#9745;
`Millisecond` | ms | `1e-3s` | &#9745;
`Second` | s | SI definition | &#9745;
`Minute` | m | `60s` | &#9745;
`Hour` | h | `60m` | &#9745;
`Day` | d | `24h` | &#9745;
`Week` | w | `7d` | &#9745;
`Month` | M | `Year / 12` | &#9744;
`Year` | y | `365.25d` | &#9744;

Note that `Months` and `Years` are not included in the default set of time units. The current
implementation uses an approximate calculation of `Months` and `Years` in seconds and if they are
included in the final configuration, the [Julian
year](https://en.wikipedia.org/wiki/Julian_year_(astronomy)) based calculation is used. (See table
above)

With the `CustomDurationParser` from the `custom` feature, the identifiers for time units can be
fully customized.

# Customization

Unlike other crates, `fundu` does not try to establish a standard for time units and their
identifiers or a specific number format. A lot of these aspects can be adjusted when
initializing or building the parser. Here's an incomplete example for possible customizations of the
number format:

```rust
use fundu::TimeUnit::*;
use fundu::{Duration, DurationParser, ParseError};

let parser = DurationParser::builder()
    // Use a custom set of time units. For demonstration purposes just NanoSecond
    .time_units(&[NanoSecond])
    // Allow some whitespace characters as delimiter between the number and the time unit
    .allow_delimiter(|byte| matches!(byte, b'\t' | b'\n' | b'\r' | b' '))
    // Makes the number optional. If no number was encountered `1` is assumed
    .number_is_optional()
    // Disable parsing the fractional part of the number => 1.0 will return an error
    .disable_fraction()
    // Disable parsing the exponent => 1e0 will return an error
    .disable_exponent()
    // Finally, build a reusable DurationParser
    .build();

// Some valid input
assert_eq!(parser.parse("ns").unwrap(), Duration::positive(0, 1));
assert_eq!(
    parser.parse("1000\t\n\r ns").unwrap(),
    Duration::positive(0, 1000)
);

// Some invalid input
assert_eq!(
    parser.parse("1.0ns").unwrap_err(),
    ParseError::Syntax(1, "No fraction allowed".to_string())
);
assert_eq!(
    parser.parse("1e9ns").unwrap_err(),
    ParseError::Syntax(1, "No exponent allowed".to_string())
);
```

Here's an example for fully-customizable time units which uses the `CustomDurationParser` from the
`custom` feature:

```rust
use fundu::TimeUnit::*;
use fundu::{CustomDurationParser, CustomTimeUnit, Duration, Multiplier, TimeKeyword};

// Let's define a custom time unit `fortnight` which is worth 2 weeks. Note the creation 
// of `CustomTimeUnits` and `TimeKeywords` can be `const` and moved to compile time:
const FORTNIGHT: CustomTimeUnit = CustomTimeUnit::new(
    Week,
    &["f", "fortnight", "fortnights"],
    Some(Multiplier(2, 0)),
);

let parser = CustomDurationParser::builder()
    .time_units(&[
        CustomTimeUnit::with_default(Second, &["s", "secs", "seconds"]),
        CustomTimeUnit::with_default(Minute, &["min"]),
        CustomTimeUnit::with_default(Hour, &["ώρα"]),
        FORTNIGHT,
    ])
    // Additionally, define `tomorrow`, a keyword of time which is worth `1 day` in the future.
    // In contrast to a `CustomTimeUnit`, a `TimeKeyword` doesn't accept a number in front of it 
    // in the source string.
    .keyword(TimeKeyword::new(Day, &["tomorrow"], Some(Multiplier(1, 0))))
    .build();

assert_eq!(
    parser.parse("42e-1ώρα").unwrap(),
    Duration::positive(15120, 0)
);
assert_eq!(
    parser.parse("tomorrow").unwrap(),
    Duration::positive(60 * 60 * 24, 0)
);
assert_eq!(
    parser.parse("1fortnight").unwrap(),
    Duration::positive(60 * 60 * 24 * 7 * 2, 0)
);
```

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

The `iai-callgrind` (feature = `with-iai`) and `flamegraph` (feature = `with-flamegraph`) benchmarks
can only be run on unix. Use the `--features` option of cargo to run the benchmarks for specific
features:

```shell
cargo bench --features standard,custom
```

The above won't run the `flamegraph` and `iai-callgrind` benchmarks.

Benchmarks can be further filtered for example with

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

To get a rough idea about the parsing times, here the average parsing speed of some inputs on a
comparatively slow machine (Quad core 3000Mhz, 8GB DDR3, Linux)

Input | avg parsing time | ~ samples / s
--- | ---:| ---:
`1` | `37.925 ns` | `26_367_831.245`
`123456789.123456789` | `50.473 ns` | `19_812_573.058`
`format!("{}.{}e-1022", "1".repeat(1022), "1".repeat(1022))` | `371.02 ns` | `2_695_272.492`

For comparison, the precision and additional features of `fundu` result in a very low performance
overhead due to the initial setup of structures, etc., and quickly catches up. Fundu even becomes
more performant than the reference function from the `stdlib` as the input gets larger (the
reference function is `Duration::from_secs_f64(input.parse().unwrap())`):

Input | avg parsing time | ~ samples / s
--- | ---:| ---:
`1` | `25.630 ns` | `39_016_777.214`
`123456789.123456789` | `45.007 ns` | `22_218_765.969`
`format!("{}.{}e-1022", "1".repeat(1022), "1".repeat(1022))` | `1.7457 µs` | `572_836.111`

# Comparison `fundu` vs `Duration::from_secs_f64`

Here's a short incomplete overview of differences and advantages of `fundu` over using
`Duration::from_secs_f64(input.parse().unwrap())` (and
`Duration::try_from_secs_f64(input.parse().unwrap())`)

Input | `fundu` | `Duration::(try_)from_secs_f64`
---:| --- | ---
`01271480964981728917.1` | `Duration::new(1_271_480_964_981_728_917, 100_000_000)` | `Duration::new(1_271_480_964_981_729_024, 0)`
`1.11111111111e10` | `Duration::new(11_111_111_111, 100_000_000)` | `Duration::new(11_111_111_111, 100_000_381)`
`1ns` | `Duration::new(0, 1)` | cannot parse time units
`"1 2e-3 3e-9"`, `1s2ms3ns` | can parse multiple durations as one `Duration::new(1, 2_000_003)` | not possible
`1000` | When changing the default unit to `MilliSecond` -> `Duration::new(1, 0)` | is always seconds based
`1e20` | `Duration::MAX` | panics or returns an error due to: `can not convert float seconds to Duration: value is either too big or NaN`
`infinity` | `Duration::MAX` | panics or returns an error due to: `can not convert float seconds to Duration: value is either too big or NaN`
`-1`, `-1s`, ... | can parse negative durations if enabled | panics or returns an error

# Platform support

Since `fundu` is purely built on top of the rust `stdlib` without platform specific code, this
library should be compatible with all platforms. Please open an issue if you find any unsupported
platforms which `rust` itself supports.

See also the [CI](https://github.com/Joining7943/fundu/actions/workflows/cicd.yml) for platforms on which `fundu` is tested.

# License

MIT license ([LICENSE](LICENSE) or <http://opensource.org/licenses/MIT>)

[`std::time::Duration`]: https://doc.rust-lang.org/std/time/struct.Duration.html
[`chrono::Duration`]: https://docs.rs/chrono/0.4.24/chrono/struct.Duration.html
[`time::Duration`]: https://docs.rs/time/latest/time/struct.Duration.html
[`Duration::MAX`]: https://doc.rust-lang.org/std/time/struct.Duration.html#associatedconstant.MAX
[`f64::from_str`]: https://doc.rust-lang.org/std/primitive.f64.html#impl-FromStr-for-f64
[`DurationParser::default_unit`]: https://docs.rs/fundu/latest/fundu/struct.DurationParser.html#method.default_unit
