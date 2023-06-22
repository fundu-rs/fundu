// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use fundu::TimeUnit::*;
use fundu::TimeUnitsLike;
use fundu_systemd::{TimeSpanParser, TimeUnitsWithNanos};

fn criterion_config() -> Criterion {
    Criterion::default()
        .nresamples(500_000)
        .sample_size(100)
        .measurement_time(Duration::from_secs(5))
}

fn get_parsing_speed_inputs() -> Vec<(String, String)> {
    vec![
        ("single digit".to_string(), "1".to_string()),
        ("mixed digits 7".to_string(), "1234567.1234567".to_string()),
        (
            "mixed digits 8".to_string(),
            "12345678.12345678".to_string(),
        ),
        (
            "mixed digits 9".to_string(),
            "123456789.123456789".to_string(),
        ),
        (
            "large input".to_string(),
            format!("{0}.{0}", "1".repeat(1022)),
        ),
    ]
}

fn benchmark_initialization(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("time span parser initialization");
    group.bench_function("new", |b| b.iter(TimeSpanParser::new));
    group.finish();
}

fn benchmark_parsing(criterion: &mut Criterion) {
    let inputs = get_parsing_speed_inputs();
    let parser = TimeSpanParser::new();
    let mut group = criterion.benchmark_group("time span parser parsing speed");
    for (parameter, input) in &inputs {
        group.bench_with_input(
            BenchmarkId::new("input without time units", parameter),
            &input,
            |b, input| b.iter(|| black_box(&parser).parse(input).unwrap()),
        );
    }
    group.finish();
}

fn benchmark_parsing_with_time_units(criterion: &mut Criterion) {
    let inputs = [
        (Minute, "m"),
        (Minute, "min"),
        (Minute, "minutes"),
        (Second, "s"),
        (Year, "y"),
        (Year, "year"),
    ];
    let parser = TimeSpanParser::new();
    let time_units = TimeUnitsWithNanos {};
    let mut group = criterion.benchmark_group("time span parser parsing speed time units");
    group.bench_with_input(
        BenchmarkId::new("get function".to_string(), "minutes"),
        "minutes",
        |b, input| b.iter(|| black_box(&time_units).get(input).unwrap()),
    );
    for (_, input) in inputs {
        group.bench_with_input(
            BenchmarkId::new("time units without number".to_string(), input),
            &input,
            |b, input| b.iter(|| black_box(&parser).parse(input).unwrap()),
        );
    }
    group.finish();
}

fn benchmark_parsing_multiple(criterion: &mut Criterion) {
    let inputs = [
        "1ns 1us",
        "1ns          1us",
        "1ns 1us 1ns 1us",
        "1ns 1us 1ms 1s",
        &"1ns 1us".repeat(100),
    ];
    let parser = TimeSpanParser::new();
    let mut group = criterion.benchmark_group("time span parser parsing speed multiple");
    for input in inputs {
        group.bench_with_input(input, &input, |b, input| {
            b.iter(|| black_box(&parser).parse_nanos(input).unwrap())
        });
    }
    group.finish();
}

criterion_group!(
    name = initialization;
    config = criterion_config();
    targets = benchmark_initialization
);
criterion_group!(
    name = parsing;
    config = criterion_config();
    targets = benchmark_parsing
);
criterion_group!(
    name = parsing_time_units;
    config = criterion_config();
    targets = benchmark_parsing_with_time_units
);
criterion_group!(
    name = parsing_multiple;
    config = criterion_config();
    targets = benchmark_parsing_multiple
);
criterion_main!(
    initialization,
    parsing,
    parsing_time_units,
    parsing_multiple
);
