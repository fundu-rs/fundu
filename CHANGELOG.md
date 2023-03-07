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
