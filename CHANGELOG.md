<!-- spell-checker: ignore millis -->

<!--
 Copyright (c) 2023 Joining7943 <joining@posteo.de>
 
 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->

<!--
Types of changes:
Added: for new features.
Changed: for changes in existing functionality.
Deprecated: for soon-to-be removed features.
Removed: for now removed features.
Fixed: for any bug fixes.
Security: in case of vulnerabilities.
-->

# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [1.2.0] - 2023-07-09

## Added

* fundu's `Duration` has now additional methods:
as_weeks, as_days, as_hours, as_minutes, as_seconds, as_millis, as_micros, as_nanos, subsec_millis, subsec_micros, subsec_nanos, extract_weeks, extract_days, extract_hours, extract_minutes, extract_seconds
* Optionally allow a delimiter between the sign and a number, time keyword etc with the
configuration option `allow_sign_delimiter` (#28)

## Changed

* When `parse_multiple` is set, a sign character can now also indicate a new duration (#24)
* Increase performance of parsing time keywords and time units without a number when
`number_is_optional` is set
* Development dependencies are updated:
    * pprof v0.11.1 -> v0.12.0
    * criterion v0.4.0 -> v0.5.1
    * rstest v0.17.0 -> v0.18.1
    * rstest_reuse v0.5.0 -> v0.6.0
* Bump fundu-core dependency from `v0.1.0` to `v0.2.0`

## Fixed

* When `parse_multiple` together with `number_is_optional` was set, then a single sign character was
interpreted as a duration of 1 second (#32)

## [1.1.0] - 2023-06-26

## Added

* `fundu` has a new feature `base` which provides greater freedom than the `custom` feature
* Implementation of `Clone` and`Hash` for `ParseError` and `TryFromDurationError`

## Changed

* Big internal restructuring which splits fundu into a `fundu-core` and `fundu` package
* Internal refactor of `fundu-core`
* The minimum supported rust version changed from `1.61.0` to `1.64.0`
* The optional `time` dependency was updated from `0.3.16` to `0.3.20`

## [1.0.0] - 2023-05-29

If upgrading from an previous version, there are some breaking changes, most notably parsing
negative durations has been completely revised. The `negative` feature was removed and the parsers
now return fundu's own `Duration`, which can represent negative `Durations`, instead of a
`std::time::Duration` (or `time::Duration`).

## Added

* A new configuration option `allow_negative` to enable parsing negative `Durations` without parsing
error
* `chrono` feature to provide methods to convert from fundu's `Duration` to `chrono::Duration` and
vice versa
* `time` feature to provide methods to convert from fundu's `Duration` to `time::Duration` and vice
versa
* `serde` feature to be able to serialize, deserialize the some important structs and enums with
`serde`: `ParseError`, `TryFromDurationError`, `Multiplier`, `Duration`
* New trait `SaturatingInto` which provides a method to convert from fundu's `Duration` into
another `Duration` saturating at the maximum or minimum of the other `Duration` instead of returning
a `TryFromDurationError`.
* A new error type `TryFromDurationError` which is returned when the conversion from fundu's
`Duration` to `std::time::Duration`, `time::Duration` or `chrono::Duration` fails.
* Add a new struct `TimeKeyword` to the `custom` feature. `TimeKeywords` (like `yesterday`) are similar
to `CustomTimeUnits` but don't accept a number in front of them in the input string.
* The `CustomDurationParser` and `CustomDurationParserBuilder` have two new methods `keyword` and
`keywords` which store `TimeKeyword`(s) in the parser.
* A new configuration option `allow_ago` was added to enable parsing the `ago` keyword in the input
string after a duration to negate the previously parsed duration
* `CustomTimeUnit::with_default`: This method creates a `CustomTimeUnit` with the default multiplier
of `Multiplier(1, 0)`
* Implementation of the standard trait `Hash` for `CustomTimeUnit`, `TimeUnit` and `Multiplier`
* New methods for `Multiplier`: `is_negative`, `is_positive`, `checked_mul`, `saturating_neg` and
the getters `coefficient` for the first component and `exponent` for the second

## Changed

* Fundu's thus far internally used `Duration` is now public and implements most standard arithmetic
traits like `Add`, `Sub` etc. It can also be converted to `std::time::Duration` and if the feature
is activated `time::Duration`, `chrono::Duration`
* BREAKING: The `DurationParser::parse` and `CustomDurationParser::parse` methods now return fundu's
own `Duration` instead of `std::time::Duration`
* BREAKING: The `Multiplier` changed from (u64, i16) to (i64, i16) to allow negative `Multipliers`
* BREAKING: The `parse_multiple` configuration option now optionally allows conjunction words (like
`and`) between durations in the input string in addition to a `Delimiter`
* BREAKING: The `DurationParserBuilder` can now build the `DurationParser` in `const` context at
compile time. To be able to do so, the methods signatures of the `DurationParserBuilder` changed
from `(&mut self) -> &mut Self` to `(mut self) -> Self`
* BREAKING: Rename `DurationParserBuilder::custom_time_units` -> `DurationParserBuilder::time_units`
* BREAKING: The `SYSTEMD_TIME_UNITS`, `DEFAULT_TIME_UNITS` and `DEFAULT_ALL_TIME_UNITS` constants
from the `custom` feature now use `CustomTimeUnit`s instead of a tuple.
* BREAKING: Remove `CustomDurationParserBuilder::time_unit` and rename
`CustomDurationParserBuilder::custom_time_unit` -> `CustomDurationParserBuilder::time_unit`
* BREAKING: Remove `CustomDurationParserBuilder::time_units` and rename
`CustomDurationParserBuilder::custom_time_units` -> `CustomDurationParserBuilder::time_units`
* BREAKING: `CustomDurationParser::with_time_units` now uses `CustomTimeUnits` instead of the
`Identifier` type
* BREAKING: Rename `CustomDurationParser::custom_time_unit` -> `CustomDurationParser::time_unit`
* BREAKING: Rename `CustomDurationParser::custom_time_units` -> `CustomDurationParser::time_units`
* BREAKING: If the setting `number_is_optional` is enabled the exponent must have a mantissa. The exponent is
now a part of the number
* Panic in `CustomTimeUnit::new` when creating a `CustomTimeUnit` with a `Multiplier` and
`TimeUnit`. A multiplication of the additional `Multiplier` and the inherent multiplier of the
`TimeUnit` would otherwise overflow (and panic) during the parsing

* Refactorings of the internal parser improve the parsing speed for all input sizes

## Removed

* BREAKING: The `negative` feature and `DurationParser::parse_negative`, `CustomDurationParser::parse_negative`
* BREAKING: The `Identifier` type is redundant and was removed

## Fixed

* Parsing with the configuration option `allow_delimiter` enabled changed, so that an input ending
with a `Delimiter` is an error now
* The exponent must always consist of at least one digit
* Input starting with a delimiter should result in a ParseError similar to input ending with a
delimiter

## [0.5.1] - 2023-05-01

This version introduces a slight performance regression in favour of the new `parse_multiple` method.

### Added

* New method `parse_multiple` to parse multiple durations in the source string at once.
* New method `disable_infinity` to disable parsing `inf` or `infinity`.
* The new methods above make it possible to build a systemd time span parser as defined by systemd
* An example for a fully functional systemd time span parser

### Changed

* Parsing `infinity` values was improved, so that time unit identifiers can now start with an `i` or `in`.
* Running the benchmarks was improved, so that `iai` (feature = `with-iai`) and `flamegraph`
(feature = `with-flamegraph`) benchmarks need to be activated via their features.
* Make `TimeUnit::multiplier` method public
* Make `custom::Identifiers` type public

### Fixed

* In the `parser` module an invocation of `ParseError::TimeUnit` error was pointing to a wrong
position in the source string.
* Use a workaround on s390x systems because parsing negative durations produced wrong results when
using `time::Duration::MIN.saturating_add`. The source of this bug is maybe the `time` crate or
`rust` itself.

## [0.5.0] - 2023-03-29

### Added

* `negative` feature: parse negative durations to a duration from the `time` crate
* The number format is now customizable:
    * allow one ore more delimiter between the number and the time unit by setting a `Delimiter`
    * disable parsing an exponent
    * disable parsing a fraction
    * make numbers in front of time units and exponents optional
* `DurationParser::builder` method and `DurationParserBuilder`
* `CustomDurationParser` allows now creating completely new `CustomTimeUnit`s
* `CustomDurationParser::builder` method and `CustomDurationParserBuilder`
* An example for the `custom` feature

### Changed

* The minimum supported rust version changed from `1.60.0` to `1.61.0`
* Some internal changes and refactorings improved the overall performance
* Improve and enhance the `README` and public api documentation

### Removed

* `DurationParser::time_unit` and `DurationParser::time_units`:
Use `DurationParser::with_time_units` or the `DurationParserBuilder` instead
* `CustomDurationParser::get_current_time_units`

## [0.4.3] - 2023-03-21

### Changed

* Change from `iai` to `iai-callgrind` and use the new features to improve the iai benchmarks

### Fixed

* Building the docs on docs.rs should use all features

## [0.4.2] - 2023-03-07

### Changed

* Internal changes to improve the overall performance but especially for large inputs.
  Parsing large inputs is now faster than the reference function.

## [0.4.1] - 2023-02-26

### Changed

* The exponent maximum/minium changed to i16 bounds.
* Make most initialization methods of `DurationParser` applicable in `const` context
* Some internal refactors improved the initialization and parsing speeds

### Fixed

* Apply cfg attributes in builder mod.rs. This fixes the warnings when not all features were given.

## [0.4.0] - 2023-02-24

### Added

* The `custom` feature adds fully customizable identifiers for time units in a new struct
  `CustomDurationParser`
* Add `cachegrind` based benchmarks in the github `CI`

### Changed

* Organize project into features: `standard` (default) and `custom`
* Include more error types in `ParseError` and make `ParseError` non exhaustive
* Improve performance of time unit parsing
* Improve and add more benchmarks

### Fixed

* The `DurationParser::parse` method used `self` mutable although this was not necessary

## [0.3.0] - 2023-02-11

### Added

* New builder method `DurationParser::default_unit` to set the default time unit to something
  different than seconds.
* New method `DurationParser::get_time_units` which returns the current set of time units.
* More runnable examples/recipes in the `examples` folder.

### Changed

* Improve the api and crate level documentation
* Update the README and api documentation to better document the handling of values close to zero no
  matter the sign.

### Removed

* Remove `TimeUnit::multiplier` from the public api. It's still used internally.

### Fixed

* Parsing the exponent if there is no number must return a `ParseError`
* Negative values exceeding `u64::MAX` returned `Duration::MAX`. Now a `ParseError` is returned.

## [0.2.2] - 2023-02-06

* Fix panic in parser when the whole and fraction part of the input number are missing but a dot is
given

## [0.2.1] - 2023-02-05

### Added

* New method `TimeUnits::get_time_units` which returns all currently active time units
* `PartialOrd, Ord` traits implementation for `TimeUnit`

### Changed

* Improve overall performance by 10-20%
* Improve performance of parsing with time units by a factor of ~15 (before ~800ns -> after ~55ns)
* tests: Improve test coverage. Reach full coverage.
* tests: Increase accuracy of benchmarks
* CI: Use `grcov` for coverage report creation with the more accurate source-based coverage

## [0.2.0] - 2023-02-03

### Added

* More tests
* Add a simple example in examples directory

### Changed

* Updated the README, library documentation and provide more examples
* Rename `DurationParser::with_no_time_units` -> `DurationParser::without_time_units`
* Change to Julian year calculation: 1 year = 365.25 days and 1 month = year / 12
* Refactor test structure
* Make the default ids of time units available

### Removed

* Unneeded constants `SECONDS_MAX` and `NANOS_MAX`

### Fixed

* Fix a possible overflow when multiplying attos with the time unit multiplier
* Export `error::ParseError` and make this enum public

## [0.1.0] - 2023-02-01

### Added

* Basic working implementation of the duration parser
* Tests and benchmarks
* A README
* Basic api documentation
* This Changelog
* CI setup with github actions
