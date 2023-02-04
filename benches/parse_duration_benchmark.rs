// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use std::time::Duration;

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use fundu::DurationParser;

fn duration_parser_benchmark(criterion: &mut Criterion) {
    let inputs = [
        ("small input", "1"),
        (
            "large input",
            &format!("{}.{}e-1022", "1".repeat(1022), "1".repeat(1022)),
        ),
    ];
    let mut parser = DurationParser::without_time_units();
    let mut group = criterion.benchmark_group("parsing speed");
    for (parameter, input) in inputs {
        group.bench_with_input(
            BenchmarkId::new("default time units", parameter),
            &input,
            |b, &input| b.iter(|| DurationParser::new().parse(black_box(input))),
        );
        group.bench_with_input(
            BenchmarkId::new("no time units", parameter),
            &input,
            |b, &input| b.iter(|| DurationParser::without_time_units().parse(black_box(input))),
        );
        group.bench_with_input(
            BenchmarkId::new("only parse", parameter),
            &input,
            |b, &input| b.iter(|| parser.parse(black_box(input))),
        );
    }
    group.finish();
}

fn reference_benchmark(criterion: &mut Criterion) {
    let inputs = [
        ("small input", "1"),
        (
            "large input",
            &format!("{}.{}e-1022", f64::MAX, "1".repeat(1022)),
        ),
    ];
    let mut group = criterion.benchmark_group("reference speed");
    for (parameter, input) in inputs {
        group.bench_with_input(
            BenchmarkId::new("reference function", parameter),
            &input,
            |b, &input| b.iter(|| Duration::from_secs_f64(black_box(input).parse().unwrap())),
        );
    }
    group.finish();
}

criterion_group!(
    name = benches;
    config = Criterion::default().sample_size(1000).measurement_time(Duration::from_secs(10));
    targets = duration_parser_benchmark, reference_benchmark
);
criterion_main!(benches);
