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

## [0.3.1] - 2023-09-07

### Changed

* Bump MSRV from `1.64.0` to `1.66.0`

## [0.3.0] - 2023-08-07

### Added

* Parse numerals like `next`, `last`, `this`, `first`, `third` etc.

### Changed

* Time units (like `sec`), keywords (like `yesterday`) and numerals (like `next`) are now parsed
case insensitive
* The parsing speed was improved significantly

## [0.2.0] - 2023-07-09

### Added

* Parsing of fuzzy `year` and `month` time units (#29)

### Changed

* A sign character can now also indicate a new duration (#24)
* A leading sign character can now be delimited by whitespace from the number or time keyword (#28)
* Bump fundu-core dependency from `v0.1.0` to `v0.2.0`

### Fixed

* A single sign character was interpreted as a duration of 1 second (#32)

## [0.1.0] - 2023-06-26

### Added

* Initial release of `fundu-gnu`
