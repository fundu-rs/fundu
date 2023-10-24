// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu::Duration;
use fundu_systemd::TimeSpanParser;
use iai_callgrind::{
    black_box, library_benchmark, library_benchmark_group, main, FlamegraphConfig,
    LibraryBenchmarkConfig,
};

#[library_benchmark]
#[bench::small(TimeSpanParser::new(), "1")]
#[bench::mixed_7(TimeSpanParser::new(), "1234567.1234567")]
#[bench::mixed_8(TimeSpanParser::new(), "12345678.12345678")]
#[bench::mixed_9(TimeSpanParser::new(), "123456789.123456789")]
#[bench::large(TimeSpanParser::new(), &format!("{0}.{0}", "1".repeat(1022)))]
fn without_time_units(parser: TimeSpanParser, input: &str) -> Duration {
    black_box(parser.parse(input)).unwrap()
}

#[library_benchmark]
#[bench::micro_second(TimeSpanParser::new(), "us")]
#[bench::second(TimeSpanParser::new(), "s")]
#[bench::minutes(TimeSpanParser::new(), "minutes")]
#[bench::year(TimeSpanParser::new(), "y")]
fn with_time_units(parser: TimeSpanParser, input: &str) -> Duration {
    black_box(parser.parse(input)).unwrap()
}

library_benchmark_group!(name = parsing_speed; benchmarks = without_time_units, with_time_units);

main!(
    config = LibraryBenchmarkConfig::default().flamegraph(FlamegraphConfig::default());
    library_benchmark_groups = parsing_speed
);
