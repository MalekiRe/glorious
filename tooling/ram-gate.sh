#!/usr/bin/env bash
# Run a memory-capped repository command. The three flock slots are shared by
# every worktree through /tmp, so expensive commands cannot overcommit a host.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/ram-gate.sh <command> [args...]

Run a non-`cargo check` command with an 8 GiB virtual-memory limit. At most
three such commands may run concurrently across Grandiose worktrees. `cargo
check` is intentionally passed through without taking a slot.
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
            ulimit -v "$ram_kib"
            exec "$@"
        fi
        eval "exec ${lock_fd}>&-"
    done
    sleep 0.1
done
