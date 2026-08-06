#!/usr/bin/env bash
# Run a memory-capped repository command. The three flock slots are shared by
# every worktree through /tmp, so expensive commands cannot overcommit a host.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/ram-gate.sh <command> [args...]

Serialize non-`cargo check` commands across at most three shared slots. Direct
commands get an 8 GiB virtual-memory limit. Cargo commands are deliberately
not virtual-memory-capped: `cargo test` and `cargo build` must let rustc finish
compilation before the produced test binary can be measured/capped separately.
`cargo check` is intentionally passed through without taking a slot.
USAGE
    exit 2
}

(($#)) || usage

# Checks are cheap enough to remain available while the three RAM slots serve
# test/build/replay work. Keep this narrow so every other invocation is gated.
if [[ $1 == cargo && ${2:-} == check ]]; then
    exec "$@"
fi

readonly lock_dir="${TMPDIR:-/tmp}/grandiose-ram-gate"
readonly ram_kib=$((8 * 1024 * 1024))
mkdir -p "$lock_dir"

# Each separately locked file is a semaphore slot. Unlike a counter, flock
# releases a slot automatically if its owner exits or is killed.
while :; do
    for slot in 1 2 3; do
        lock_file="$lock_dir/slot-$slot.lock"
        exec {lock_fd}>"$lock_file"
        if flock -n "$lock_fd"; then
            export G1_TEST_MEMORY_CAPPED=1
            # A single self-host integration test can approach the 8 GiB cap;
            # keep Rust's in-process test harness serial unless a caller has
            # explicitly measured and overridden it.
            export RUST_TEST_THREADS="${RUST_TEST_THREADS:-1}"
            # Do not cap cargo itself: rustc can require more virtual address
            # space while building a test than the test process needs at run
            # time.  The gate still serializes it.  Direct commands remain
            # capped for measured runtime enforcement.
            if [[ $1 != cargo ]]; then
                ulimit -v "$ram_kib"
            fi
            exec "$@"
        fi
        eval "exec ${lock_fd}>&-"
    done
    sleep 0.1
done
