#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
grandiose="$root/target/release/grandiose"

memory_limit_mib="${GRANDIOSE_MEMORY_LIMIT_MIB:-4096}"
max_eval_frames="${GRANDIOSE_MAX_EVAL_FRAMES:-4000000}"
telemetry_seconds="${GRANDIOSE_TELEMETRY_SECONDS:-600}"
program="${1:-$root/compiler/src/main.gr}"
input="${2:-$root/compiler/src/main.gr}"
output="${3:-/tmp/grandiose-self.ll}"

if [[ ! -x "$grandiose" ]]; then
    printf 'missing release interpreter: run `cargo build --release -p grandiose`\n' >&2
    exit 2
fi

if ! [[ "$memory_limit_mib" =~ ^[1-9][0-9]*$ ]]; then
    printf 'GRANDIOSE_MEMORY_LIMIT_MIB must be a positive integer\n' >&2
    exit 2
fi

if ! [[ "$max_eval_frames" =~ ^[1-9][0-9]*$ ]]; then
    printf 'GRANDIOSE_MAX_EVAL_FRAMES must be a positive integer\n' >&2
    exit 2
fi

if ! [[ "$telemetry_seconds" =~ ^[1-9][0-9]*$ ]]; then
    printf 'GRANDIOSE_TELEMETRY_SECONDS must be a positive integer\n' >&2
    exit 2
fi

# A failed self-host must not be able to consume the workstation or write a
# multi-gigabyte core file. The bootstrap has no wall-clock limit; the memory
# and evaluator-frame ceilings remain hard safety boundaries.
ulimit -c 0
ulimit -S -v "$((memory_limit_mib * 1024))"

exec env GRANDIOSE_MAX_EVAL_FRAMES="$max_eval_frames" \
    GRANDIOSE_TELEMETRY_SECONDS="$telemetry_seconds" \
    GRANDIOSE_BOOTSTRAP_FAST_PATHS=1 \
    "$grandiose" "$program" -- "$input" "$output"
