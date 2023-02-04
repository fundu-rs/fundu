// Copyright (c) 2023 Joining7943 <joining@posteo.de>
//
// This software is released under the MIT License.
// https://opensource.org/licenses/MIT

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fundu::DurationParser;
use pprof::criterion::{Output, PProfProfiler};

fn flame_graph_for_small_input(criterion: &mut Criterion) {
    let input = "1";
    let mut parser = DurationParser::without_time_units();
    criterion.bench_function("flamegraph_small_input", |b| {
        b.iter(|| parser.parse(black_box(input)))
    });
}

criterion_group!(
    name = benches;
    config = Criterion::default().with_profiler(PProfProfiler::new(1_000_000, Output::Flamegraph(None)));
    targets = flame_graph_for_small_input
);
criterion_main!(benches);
