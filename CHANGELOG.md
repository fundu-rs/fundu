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

## [0.2.1] - 2023-02-05

### Added

- New method `TimeUnits::get_time_units` which returns all currently active time units
- `PartialOrd, Ord` traits implementation for `TimeUnit`

### Changed

- Improve overall performance by 10-20%
- Improve performance of parsing with time units by a factor of ~15 (before ~800ns -> after ~55ns)
- tests: Improve test coverage
- tests: Increase accuracy of benchmarks
- CI: Use `grcov` for coverage report creation with the more accurate source-based coverage

## [0.2.0] - 2023-02-03

### Added

- More tests
- Add a simple example in examples directory

### Changed

- Updated the README, library documentation and provide more examples
- Rename `DurationParser::with_no_time_units` -> `DurationParser::without_time_units`
- Change to Julian year calculation: 1 year = 365.25 days and 1 month = year / 12
- Refactor test structure
- Make the default ids of time units available

### Removed

- Unneeded constants `SECONDS_MAX` and `NANOS_MAX`

### Fixed

- Fix a possible overflow when multiplying attos with the time unit multiplier
- Export `error::ParseError` and make this enum public

## [0.1.0] - 2023-02-01

### Added

- Basic working implementation of the duration parser
- Tests and benchmarks
- A README
- Basic api documentation
- This Changelog
- CI setup with github actions
