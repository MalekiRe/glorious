#!/usr/bin/env bash
# Serialize expensive test/replay commands across three shared flock slots.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/ram-gate.sh <command> [args...]

`cargo build` and `cargo check` deliberately pass through: compilation may run
freely. Every `cargo test` invocation must use this gate; at most three may
run concurrently across Grandiose worktrees and each receives a 16 GiB
virtual-memory limit. Other direct commands retain the 8 GiB limit.
USAGE
    exit 2
}

(($#)) || usage

# Builds/checks are permitted without slots or a virtual-memory limit.  Keep
# this explicit: agents must invoke `cargo test` through this script instead.
if [[ $1 == cargo && ( ${2:-} == check || ${2:-} == build ) ]]; then
    exec "$@"
fi

readonly lock_dir="${TMPDIR:-/tmp}/grandiose-ram-gate"
readonly direct_ram_kib=$((8 * 1024 * 1024))
readonly cargo_test_ram_kib=$((16 * 1024 * 1024))
mkdir -p "$lock_dir"

# Each separately locked file is a semaphore slot. Unlike a counter, flock
# releases a slot automatically if its owner exits or is killed.
while :; do
    for slot in 1 2 3; do
        lock_file="$lock_dir/slot-$slot.lock"
        exec {lock_fd}>"$lock_file"
        if flock -n "$lock_fd"; then
            export G1_TEST_MEMORY_CAPPED=1
            if [[ $1 == cargo && ${2:-} == test ]]; then
                export RUST_TEST_THREADS="${RUST_TEST_THREADS:-1}"
                ulimit -v "$cargo_test_ram_kib"
            elif [[ $1 != cargo ]]; then
                ulimit -v "$direct_ram_kib"
            fi
            exec "$@"
        fi
        eval "exec ${lock_fd}>&-"
    done
    sleep 0.1
done
