# spell-checker: ignore grcov profdata rustfilt

baseline_features := 'standard,custom,time,chrono,serde,base'

# List the curated project commands
[group('help')]
default:
    @just --list

# Check dependencies for policy and security issues (Uses: 'cargo-deny')
[group('dependencies')]
deny:
    cargo deny check

# Check the workspace with minimal dependency versions (Uses: 'cargo-minimal-versions')
[group('dependencies')]
minimal-versions:
    cargo minimal-versions check --workspace --ignore-private --all-features --lib --bins

# Check Rust formatting with nightly rustfmt
[group('formatting')]
check-fmt:
    cargo +nightly fmt --check

# Build with the selected feature set
[group('build')]
build features=baseline_features:
    cargo build --features "{{ features }}"

# Run stable Clippy with the selected feature set
[group('lint')]
stable-clippy features=baseline_features:
    cargo +stable clippy --features "{{ features }}" --all-targets -- -D warnings

# Run tests with the selected feature set
[group('test')]
test features=baseline_features:
    cargo test --features "{{ features }}"

# Run all documentation tests
[group('documentation')]
doc-test:
    cargo test --all-features --doc -- --show-output

# Build documentation with stable Rust
[group('documentation')]
doc:
    cargo +stable doc --all-features --no-deps --document-private-items

# Build a target with Cross and a temporary configuration (Uses: 'cross')
[group('cross')]
cross-build target:
    #!/usr/bin/env bash
    set -euo pipefail
    cross_config="$(mktemp)"
    trap 'rm -f "$cross_config"' EXIT
    cat >"$cross_config" <<'EOF'
    [build.env]
    passthrough = ["CI", "RUST_BACKTRACE", "CARGO_TERM_COLOR", "CARGO_REGISTRIES_CRATES_IO_PROTOCOL", "CARGO_INCREMENTAL"]
    EOF
    CROSS_CONFIG="$cross_config" cross build --features "{{ baseline_features }}" --target "{{ target }}"

# Test a target with Cross and a temporary configuration (Uses: 'cross')
[group('cross')]
cross-test target:
    #!/usr/bin/env bash
    set -euo pipefail
    cross_config="$(mktemp)"
    trap 'rm -f "$cross_config"' EXIT
    cat >"$cross_config" <<'EOF'
    [build.env]
    passthrough = ["CI", "RUST_BACKTRACE", "CARGO_TERM_COLOR", "CARGO_REGISTRIES_CRATES_IO_PROTOCOL", "CARGO_INCREMENTAL"]
    EOF
    CROSS_CONFIG="$cross_config" cross test --features "{{ baseline_features }}" --target "{{ target }}"

# Remove coverage build and profile data
[group('coverage')]
coverage-clean:
    #!/usr/bin/env bash
    set -euo pipefail
    cargo clean
    find . -type f -name '*.profraw' -delete

# Build with the coverage profile without writing Cargo configuration
[group('coverage')]
coverage-build $RUSTFLAGS='-C instrument-coverage' $LLVM_PROFILE_FILE='fundu_coverage-%p-%m.profraw':
    cargo --config 'profile.coverage.inherits="dev"' --config profile.coverage.lto=false --config profile.coverage.debug=true --config profile.coverage.opt-level=0 build --features "{{ baseline_features }}" --profile coverage

# Run integration tests with the coverage profile without writing Cargo configuration
[group('coverage')]
coverage-test $RUSTFLAGS='-C instrument-coverage' $LLVM_PROFILE_FILE='fundu_coverage-%p-%m.profraw':
    cargo --config 'profile.coverage.inherits="dev"' --config profile.coverage.lto=false --config profile.coverage.debug=true --config profile.coverage.opt-level=0 test --features "{{ baseline_features }}" --tests --profile coverage

# Generate file and LCOV coverage reports (Uses: 'grcov')
[group('coverage')]
coverage-report:
    #!/usr/bin/env bash
    set -euo pipefail
    grcov . \
        --llvm-path /usr/bin \
        --binary-path target/coverage \
        --ignore-not-existing \
        --output-type files \
        --excl-start 'cov:\s*excl-start' \
        --excl-stop 'cov:\s*excl-stop' \
        --excl-line '^\s*((debug_)?assert(_eq|_ne)?!|#\[derive\(|.*cov:\s*excl-line)' \
        --ignore '**/examples/*' \
        --ignore '/*' \
        --ignore '[a-zA-Z]:/*' \
        --source-dir . | sort -u
    grcov . \
        --branch \
        --llvm-path /usr/bin \
        --binary-path target/coverage \
        --ignore-not-existing \
        --output-type lcov \
        --source-dir . \
        --excl-start 'cov:\s*excl-start' \
        --excl-stop 'cov:\s*excl-stop' \
        --excl-line '^\s*((debug_)?assert(_eq|_ne)?!|#\[derive\(|.*cov:\s*excl-line)' \
        --ignore '**/examples/*' \
        --ignore '/*' \
        --ignore '[a-zA-Z]:/*' \
        --output-path lcov.info
    test -e lcov.info

# Run the complete coverage workflow in order
[group('coverage')]
coverage:
    just coverage-clean
    just coverage-build
    just coverage-test
    just coverage-report

# Fuzz a target, using its dictionary when present (Uses: 'cargo-fuzz')
[group('fuzzing')]
fuzz-run package fuzz_target duration='60' $RUSTFLAGS='-C instrument-coverage' $LLVM_PROFILE_FILE='fundu_fuzzy_coverage-%p-%m.profraw':
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{ package }}/fuzz"
    args=(run --all-features "{{ fuzz_target }}" --
        "-max_total_time={{ duration }}"
        -print_final_stats=1
        -print_corpus_stats=1
        -verbosity=2)
    dictionary="dicts/{{ fuzz_target }}.dict"
    if [[ -f "$dictionary" ]]; then
        args+=("-dict=$dictionary")
    fi
    cargo fuzz "${args[@]}"

# Build fuzz coverage data for a target (Uses: 'cargo-fuzz')
[group('fuzzing')]
fuzz-coverage package fuzz_target $RUSTFLAGS='-C instrument-coverage' $LLVM_PROFILE_FILE='fundu_fuzzy_coverage-%p-%m.profraw':
    cd "{{ package }}/fuzz" && cargo fuzz coverage "{{ fuzz_target }}"

# Export an LCOV report for a fuzz target (Uses: 'llvm-cov', 'rustfilt')
[group('fuzzing')]
fuzz-report package fuzz_target:
    #!/usr/bin/env bash
    set -euo pipefail
    cd "{{ package }}/fuzz"
    llvm_cov_bin="$(realpath -e "$(rustc --print target-libdir)"/../bin/llvm-cov)"
    "$llvm_cov_bin" export \
        "target/x86_64-unknown-linux-gnu/coverage/x86_64-unknown-linux-gnu/release/{{ fuzz_target }}" \
        --instr-profile="coverage/{{ fuzz_target }}/coverage.profdata" \
        --format=lcov \
        --ignore-filename-regex='/rustc/.*|\.cargo/registry/.*|fuzz/fuzz_targets/.*' \
        -Xdemangler=rustfilt > lcov.info
    test -e lcov.info

# Discover and run all Gungraun benchmarks (Uses: 'jq', 'cargo')
[group('benchmarks')]
bench:
    #!/usr/bin/env bash
    set -euo pipefail
    benches="$(
        cargo metadata --no-deps --format-version=1 \
            | jq -r '.packages[].targets[] | select(any(.kind[]; . == "bench") and (."required-features" and any(."required-features"[]; . == "with-gungraun"))) | .name'
    )"
    args=()
    while IFS= read -r bench; do
        [[ -n "$bench" ]] || continue
        args+=(--bench "$bench")
    done <<<"$benches"
    if (( ${#args[@]} == 0 )); then
        echo 'No Gungraun benchmarks found' >&2
        exit 1
    fi
    cargo bench --all-features "${args[@]}"

# Run Miri tests for the native target
[group('miri')]
miri:
    cargo +nightly miri setup
    cargo +nightly miri test --features "{{ baseline_features }}"

# Run Miri tests for a cross target with a temporary configuration (Uses: 'cross')
[group('miri')]
cross-miri target:
    #!/usr/bin/env bash
    set -euo pipefail
    cargo +nightly miri setup
    cross_config="$(mktemp)"
    trap 'rm -f "$cross_config"' EXIT
    cat >"$cross_config" <<'EOF'
    [build.env]
    passthrough = ["CI", "RUST_BACKTRACE", "CARGO_TERM_COLOR", "CARGO_REGISTRIES_CRATES_IO_PROTOCOL", "CARGO_INCREMENTAL"]
    EOF
    RUSTUP_TOOLCHAIN=nightly CROSS_CONFIG="$cross_config" cross miri test --features "{{ baseline_features }}" --target "{{ target }}"
