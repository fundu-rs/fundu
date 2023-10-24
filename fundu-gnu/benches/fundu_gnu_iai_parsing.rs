// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use fundu_gnu::{Duration, RelativeTimeParser};
use iai_callgrind::{
    black_box, library_benchmark, library_benchmark_group, main, FlamegraphConfig,
    LibraryBenchmarkConfig,
};

#[library_benchmark]
#[bench::small(RelativeTimeParser::new(), "1")]
#[bench::mixed_7(RelativeTimeParser::new(), "1234567")]
#[bench::mixed_8(RelativeTimeParser::new(), "12345678")]
#[bench::mixed_9(RelativeTimeParser::new(), "123456789")]
#[bench::large(RelativeTimeParser::new(), &format!("{0}.{0}", "1".repeat(1022)))]
fn inputs(parser: RelativeTimeParser, input: &str) -> Duration {
    black_box(parser.parse(input)).unwrap()
}

#[library_benchmark]
#[bench::one_sec(RelativeTimeParser::new(), "1sec")]
#[bench::sec(RelativeTimeParser::new(), "sec")]
#[bench::one_seconds(RelativeTimeParser::new(), "1seconds")]
#[bench::seconds(RelativeTimeParser::new(), "seconds")]
#[bench::one_min(RelativeTimeParser::new(), "1min")]
#[bench::min(RelativeTimeParser::new(), "min")]
#[bench::one_minutes(RelativeTimeParser::new(), "1minutes")]
#[bench::minutes(RelativeTimeParser::new(), "minutes")]
#[bench::one_day(RelativeTimeParser::new(), "1day")]
#[bench::day(RelativeTimeParser::new(), "day")]
fn with_time_units(parser: RelativeTimeParser, input: &str) -> Duration {
    black_box(parser.parse(input)).unwrap()
}

library_benchmark_group!(name = parsing_speed; benchmarks = inputs, with_time_units);

main!(
    config = LibraryBenchmarkConfig::default().flamegraph(FlamegraphConfig::default());
    library_benchmark_groups = parsing_speed
);
