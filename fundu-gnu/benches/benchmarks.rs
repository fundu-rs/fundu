// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use fundu_gnu::RelativeTimeParser;

fn criterion_config() -> Criterion {
    Criterion::default()
        .nresamples(500_000)
        .sample_size(100)
        .measurement_time(Duration::from_secs(5))
}

fn get_parsing_speed_inputs() -> Vec<(String, String)> {
    vec![
        ("single digit".to_string(), "1".to_string()),
        (
            "mixed digits 7 no fraction".to_string(),
            "1234567".to_string(),
        ),
        (
            "mixed digits 8 no fraction".to_string(),
            "12345678".to_string(),
        ),
        (
            "mixed digits 9 no fraction".to_string(),
            "123456789".to_string(),
        ),
        ("large input no fraction".to_string(), "1".repeat(1022)),
    ]
}

fn benchmark_initialization(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("relative time parser initialization");
    group.bench_function("new", |b| b.iter(RelativeTimeParser::new));
    group.finish();
}

fn benchmark_parsing(criterion: &mut Criterion) {
    let inputs = get_parsing_speed_inputs();
    let parser = RelativeTimeParser::new();
    let mut group = criterion.benchmark_group("relative time parser parsing speed");
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
    let inputs = ["sec", "seconds", "min", "minutes", "year"];
    let parser = RelativeTimeParser::new();
    let mut group = criterion.benchmark_group("relative time parser parsing speed time units");
    for input in inputs {
        group.bench_with_input(
            BenchmarkId::new("time unit without number".to_string(), input),
            &input,
            |b, input| b.iter(|| black_box(&parser).parse(input).unwrap()),
        );
        let input = &format!("1{input}");
        group.bench_with_input(
            BenchmarkId::new("time unit with number".to_string(), input),
            &input,
            |b, input| b.iter(|| black_box(&parser).parse(input).unwrap()),
        );
    }
    group.finish();
}

fn benchmark_parsing_years(criterion: &mut Criterion) {
    let inputs = ["1year", "10year", "10000000year"];
    let parser = RelativeTimeParser::new();
    let mut group = criterion.benchmark_group("relative time parser parsing speed year");
    for input in inputs {
        group.bench_with_input(input, &input, |b, input| {
            b.iter(|| black_box(&parser).parse(input).unwrap())
        });
    }
    group.finish();
}

fn benchmark_parsing_multiple(criterion: &mut Criterion) {
    let inputs = [
        "1sec 1min",
        "1sec          1min",
        "1sec 1min 1sec 1min",
        "1sec 1min 1hour 1day",
        &"1sec 1min".repeat(100),
    ];
    let parser = RelativeTimeParser::new();
    let mut group = criterion.benchmark_group("relative time parser parsing speed multiple");
    for input in inputs {
        group.bench_with_input(input, &input, |b, input| {
            b.iter(|| black_box(&parser).parse(input).unwrap())
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
criterion_group!(
    name = parsing_years;
    config = criterion_config();
    targets = benchmark_parsing_years
);
criterion_main!(
    initialization,
    parsing,
    parsing_time_units,
    parsing_multiple,
    parsing_years
);
