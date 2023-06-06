// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use fundu::TimeUnit::*;
use fundu::TimeUnitsLike;
use fundu_systemd::{TimeSpanParser, TimeUnits};

fn criterion_config() -> Criterion {
    Criterion::default()
        .nresamples(500_000)
        .sample_size(100)
        .measurement_time(Duration::from_secs(5))
}

fn get_parsing_speed_inputs() -> Vec<(String, String)> {
    vec![
        ("single digit".to_string(), "1".to_string()),
        ("mixed digits 7".to_string(), "1234567".to_string()),
        ("mixed digits 8".to_string(), "12345678".to_string()),
        ("mixed digits 9".to_string(), "123456789".to_string()),
        ("large input".to_string(), "1".repeat(1022)),
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
    for (parameter, input) in inputs {
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
        (NanoSecond, "nsec"),
        (Year, "year"),
    ];
    let parser = TimeSpanParser::new();
    let time_units = TimeUnits {};
    let mut group = criterion.benchmark_group("time span parser parsing speed time units");
    group.bench_with_input(
        BenchmarkId::new("get function".to_string(), "minutes"),
        "minutes",
        |b, input| b.iter(|| black_box(&time_units).get(input).unwrap()),
    );
    for (_, input) in inputs {
        group.bench_with_input(
            BenchmarkId::new("parse function".to_string(), input),
            &input,
            |b, input| b.iter(|| black_box(&parser).parse(input).unwrap()),
        );
    }
    group.finish();
}

// fn reference_benchmark(criterion: &mut Criterion) {
//     let inputs = get_parsing_speed_inputs();
//     let mut group = criterion.benchmark_group("reference speed");
//     for (parameter, input) in inputs {
//         group.bench_with_input(
//             BenchmarkId::new("reference function", parameter),
//             &input,
//             |b, input| b.iter(|| Duration::from_secs_f64(input.parse().unwrap())),
//         );
//     }
//     group.finish();
// }

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
// criterion_group!(
//     name = parsing_infinity;
//     config = criterion_config();
//     targets = benchmark_parsing_infinity
// );
criterion_group!(
    name = parsing_time_units;
    config = criterion_config();
    targets = benchmark_parsing_with_time_units
);
// criterion_group!(
//     name = reference;
//     config = criterion_config();
//     targets = reference_benchmark
// );
criterion_main!(
    initialization,
    parsing,
    // parsing_infinity,
    // reference,
    parsing_time_units
);
