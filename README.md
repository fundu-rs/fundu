<!--
 Copyright (c) 2023 Joining <joining@posteo.de>
 
 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<h1 align="center">Configurable, precise and fast string parser to a rust std::time::Duration</h1>

`fundu` (reads like `fun with duration`) provides a duration parser to parse strings into a [`std::time::Duration`]. It tries to improve on the standard method `Duration::from_secs_f64(input.parse().unwrap())` by

* Providing customizable [`TimeUnit`]s which are accepted in the input string. See table below.
* Using no floating point calculations and precisely parse the input as it is. So, what you put
in you is what you get out within the range of a `std::time::Duration`.
* Evaluating to `std::time::Duration::MAX` if the input number was larger than that maximum or
the input string was positive `infinity`
* Providing better error messages in case of parsing errors.

These features come with almost no additional runtime costs by still being a lightweight crate.
This crate is built on top of the rust `stdlib`, and no additional dependencies are required. The
accepted number format is almost the same like the scientific floating point format by being compatible to the `f64` format. In other words, if the accepted format was `f64` before there is no change needed to accept the same format with `fundu`. For further details
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

When a customization of the accepted [`TimeUnit`]s is required then the builder
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

Name | Accepted Time unit | `DurationParser::new` \| `parse_duration` | `DurationParser::with_all_time_units` | `DurationParser::with_no_time_units`
--- | --- | --- | --- | ---
Nanoseconds | ns | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Microseconds | Ms | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Milliseconds | ms | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Seconds | s | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Minutes | m | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Hours | h | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Days | d | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Weeks | w | :heavy_check_mark: | :heavy_check_mark: | :white_large_square:
Months | M | :white_large_square: | :heavy_check_mark: | :white_large_square:
Years | y | :white_large_square: | :heavy_check_mark: | :white_large_square:

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
