<!--
 Copyright (c) 2023 Joining7943 <joining@posteo.de>
 
 This software is released under the MIT License.
 https://opensource.org/licenses/MIT
-->
# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- Add more unit tests
- Add a simple example in examples directory

### Changed

- Updated the README, library documentation and provide more examples
- Rename `DurationParser::with_no_time_units` -> `DurationParser::without_time_units`
- Change to Julian year calculation: 1 year = 365.25 days and 1 month = year / 12

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
