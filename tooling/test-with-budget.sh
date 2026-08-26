#!/usr/bin/env bash
# All repository test invocations use this guard. Leave a small reporting
# margin below the CI job's ten-minute ceiling.
set -euo pipefail

readonly maximum_seconds="${GRANDIOSE_TEST_TIMEOUT_SECONDS:-590}"

# The termination grace below is part of the test runtime budget. Keeping the
# command timeout at most 590 seconds makes the absolute ceiling 600 seconds.
if ! [[ "$maximum_seconds" =~ ^[1-9][0-9]*$ ]] || (( maximum_seconds > 590 )); then
    echo "test-with-budget: timeout must be an integer from 1 to 590 seconds" >&2
    exit 2
fi

if (( $# == 0 )); then
    echo "usage: tooling/test-with-budget.sh COMMAND [ARGUMENT]..." >&2
    exit 2
fi

# Run the command in timeout's managed process group.  Do not use
# `--foreground`: that mode intentionally avoids the separate group and can
# leave workers spawned by a test runner alive after the parent is killed.
# The short grace period keeps the total hard ceiling at ten minutes while
# preserving an ordinary command exit status.
exec timeout --kill-after=10s --preserve-status "${maximum_seconds}s" "$@"
