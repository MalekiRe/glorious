#!/usr/bin/env bash
# Benchmark an already-built libtest binary: Rust rebuild time is separate.
set -euo pipefail

if (( $# < 1 || $# > 2 )); then
    echo "usage: bash tooling/benchmark-stage0.sh TEST_BINARY [TEST_FILTER]" >&2
    exit 2
fi

readonly benchmark_binary="$1"
readonly benchmark_filter="${2:-service_infers}"
readonly benchmark_runs="${G1_BENCH_RUNS:-5}"
if [[ ! -f "$benchmark_binary" || ! -x "$benchmark_binary" ]]; then
    echo "benchmark: expected an existing executable test binary" >&2
    exit 2
fi
if ! [[ "$benchmark_runs" =~ ^[1-9][0-9]?$ ]] || (( benchmark_runs > 20 )); then
    echo "benchmark: G1_BENCH_RUNS must be between 1 and 20" >&2
    exit 2
fi

# A misspelled filter must not produce a deceptively fast zero-test result.
inventory=$("$benchmark_binary" "$benchmark_filter" --list)
if ! rg ': test$' <<<"$inventory"; then
    echo "benchmark: filter selected no tests" >&2
    exit 2
fi
sha256sum -- "$benchmark_binary"

TIMEFORMAT='wall_seconds=%R user_seconds=%U system_seconds=%S'

for ((run = 1; run <= benchmark_runs; run++)); do
    echo "benchmark run $run/$benchmark_runs" >&2
    time tooling/test-with-budget.sh tooling/ram-gate.sh \
        "$benchmark_binary" "$benchmark_filter" --test-threads=1 --quiet
done
