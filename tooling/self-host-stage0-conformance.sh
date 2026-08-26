#!/usr/bin/env bash
# Runs the complete current self-host source conformance suite after one
# incremental Stage0 build, keeping the CI gate comfortably below its budget.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# CI wraps this script too, but direct local invocation must obey the same
# hard ceiling. The marker avoids recursively launching the guard.
if [[ "${GRANDIOSE_SELF_HOST_CONFORMANCE_GUARDED:-0}" != 1 ]]; then
    exec env GRANDIOSE_SELF_HOST_CONFORMANCE_GUARDED=1 \
        "$root/tooling/test-with-budget.sh" "$0" "$@"
fi

# Callers that have already built the Stage0 binary (notably CI's outer
# budgeted invocation) must not pay for a second identical build. Individual
# checks already honor this marker, so keep the suite-level behavior aligned.
if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi
if [[ "${GRANDIOSE_GRVM_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-vm --bin grvm
fi

GRANDIOSE_STAGE0_ALREADY_BUILT=1 "$root/tooling/self-host-stage0-canonical-world-check.sh"
"$root/tooling/self-host-stage0-lib-inventory-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/service_staged_publication.glorious" GRANDIOSE_STAGE0_SERVICE_EXPECTED=114 "$root/tooling/self-host-stage0-service-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/service_cancellation_dispatch.glorious" GRANDIOSE_STAGE0_SERVICE_EXPECTED=201 "$root/tooling/self-host-stage0-service-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/service_compile.glorious" GRANDIOSE_STAGE0_SERVICE_EXPECTED=222227511111122211 "$root/tooling/self-host-stage0-service-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 "$root/tooling/self-host-stage0-bootstrap-artifact-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 "$root/tooling/self-host-stage0-process-args-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 "$root/tooling/self-host-stage0-main-process-args-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 "$root/tooling/self-host-stage0-file-read-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 "$root/tooling/self-host-stage0-service-file-read-check.sh"
GRANDIOSE_STAGE0_ALREADY_BUILT=1 "$root/tooling/self-host-stage0-diagnostic-write-check.sh"

# Each remaining check owns a distinct probe/artifact path and only reads the
# already-built Stage0 binary.  Running a small bounded batch removes the
# repeated process-startup wall time without turning the conformance gate into
# an unbounded host-resource consumer.  Keep the earlier artifact/CLI checks
# isolated by their own temporary directories and only read the already-built
# Stage0/VM binaries, so they can share the bounded parallel batch safely.
readonly parallel_jobs="${GRANDIOSE_SELF_HOST_CONFORMANCE_JOBS:-4}"
if ! [[ "$parallel_jobs" =~ ^[1-9][0-9]*$ ]] || (( parallel_jobs > 8 )); then
    echo "self-host conformance: GRANDIOSE_SELF_HOST_CONFORMANCE_JOBS must be 1 through 8" >&2
    exit 2
fi
declare -a check_pids=()

for check in \
    self-host-stage0-g1-default-artifact-check.sh \
    self-host-stage0-g1-source-unit-artifact-check.sh \
    self-host-stage0-g1-file-unit-artifact-check.sh \
    self-host-stage0-g1-cli-emit-vm-check.sh \
    self-host-stage0-g1-cli-verify-vm-check.sh \
    self-host-stage0-branch-bool-check.sh \
    self-host-stage0-wrapping-add-check.sh \
    self-host-stage0-wrapping-mul-check.sh \
    self-host-stage0-checked-div-check.sh \
    self-host-stage0-bootstrap-indirection-check.sh \
    self-host-stage0-blake3-check.sh \
    self-host-stage0-cancellation-check.sh \
    self-host-stage0-cancellation-result-check.sh \
    self-host-stage0-budget-check.sh \
    self-host-stage0-budget-charge-check.sh \
    self-host-stage0-transaction-check.sh \
    self-host-stage0-publication-check.sh \
    self-host-stage0-quantity-check.sh \
    self-host-stage0-quantity-contains-check.sh \
    self-host-stage0-quantity-hull-check.sh \
    self-host-stage0-quantity-intersection-check.sh \
    self-host-stage0-quantity-sequence-check.sh \
    self-host-stage0-quantity-multiply-check.sh \
    self-host-stage0-quantity-construction-check.sh \
    self-host-stage0-diagnostic-check.sh \
    self-host-stage0-header-check.sh \
    self-host-stage0-high-arity-check.sh \
    self-host-stage0-request-check.sh \
    self-host-stage0-bootstrap-stage-check.sh \
    self-host-stage0-interface-check.sh \
    self-host-stage0-fixity-check.sh \
    self-host-stage0-module-graph-check.sh \
    self-host-stage0-resolution-check.sh \
    self-host-stage0-types-check.sh \
    self-host-stage0-signature-check.sh \
    self-host-stage0-coherence-check.sh \
    self-host-stage0-trait-solver-check.sh \
    self-host-stage0-pattern-check.sh \
    self-host-stage0-body-check.sh \
    self-host-stage0-core-check.sh \
    self-host-stage0-placeflow-check.sh \
    self-host-stage0-useflow-check.sh \
    self-host-stage0-escape-check.sh \
    self-host-stage0-mir-storage-check.sh \
    self-host-stage0-instance-check.sh \
    self-host-stage0-mir-check.sh \
    self-host-stage0-vm-backend-check.sh \
    self-host-stage0-runtime-manifest-check.sh \
    self-host-stage0-bootstrap-check.sh \
    self-host-stage0-dependency-check.sh \
    self-host-stage0-revision-check.sh \
    self-host-stage0-query-check.sh \
    self-host-stage0-artifact-cache-check.sh \
    self-host-stage0-service-check.sh \
    self-host-stage0-service-named-header-check.sh \
    self-host-stage0-service-function-body-check.sh \
    self-host-stage0-service-literal-check.sh \
    self-host-stage0-lib-check.sh \
    self-host-stage0-main-check.sh \
    self-host-stage0-output-check.sh \
    self-host-stage0-output-write-check.sh \
    self-host-stage0-source-check.sh \
    self-host-stage0-scanner-check.sh; do
    GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_GRVM_ALREADY_BUILT=1 "$root/tooling/$check" &
    check_pids+=("$!")
    if (( ${#check_pids[@]} >= parallel_jobs )); then
        wait "${check_pids[0]}"
        check_pids=("${check_pids[@]:1}")
    fi
done

for check_pid in "${check_pids[@]}"; do
    wait "$check_pid"
done
