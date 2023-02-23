// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use fundu::{CustomDurationParser, DEFAULT_ALL_TIME_UNITS, SYSTEMD_TIME_UNITS};

fn duration_parser_initialization(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("custom duration parser initialization");
    group.bench_function("without time units", |b| b.iter(CustomDurationParser::new));
    group.bench_with_input(
        "default time units",
        &DEFAULT_ALL_TIME_UNITS,
        |b, time_units| b.iter(|| CustomDurationParser::with_time_units(time_units)),
    );
    group.bench_with_input(
        "systemd time units",
        &SYSTEMD_TIME_UNITS,
        |b, time_units| b.iter(|| CustomDurationParser::with_time_units(time_units)),
    );
    group.finish();
}

fn duration_parser_parsing_speed(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("custom duration parser parsing speed");
    // let no_time_units_parser = CustomDurationParser::new();
    let input = "1";
    group.bench_with_input(
        BenchmarkId::new("without time units", input),
        &(CustomDurationParser::new(), input),
        |b, (parser, input)| b.iter(|| parser.parse(input)),
    );
    let input = "1";
    group.bench_with_input(
        BenchmarkId::new("default time units", input),
        &(
            CustomDurationParser::with_time_units(&DEFAULT_ALL_TIME_UNITS),
            input,
        ),
        |b, (parser, input)| b.iter(|| parser.parse(input)),
    );
    let input = "1y";
    group.bench_with_input(
        BenchmarkId::new("default time units", input),
        &(
            CustomDurationParser::with_time_units(&DEFAULT_ALL_TIME_UNITS),
            input,
        ),
        |b, (parser, input)| b.iter(|| parser.parse(input)),
    );
    let input = "1years";
    group.bench_with_input(
        BenchmarkId::new("systemd time units", input),
        &(
            CustomDurationParser::with_time_units(&SYSTEMD_TIME_UNITS),
            input,
        ),
        |b, (parser, input)| b.iter(|| parser.parse(input)),
    );
    group.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default().sample_size(1000).measurement_time(Duration::from_secs(10));
    targets = duration_parser_initialization, duration_parser_parsing_speed
);
criterion_main!(benches);
