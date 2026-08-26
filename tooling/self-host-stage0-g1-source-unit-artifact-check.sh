#!/usr/bin/env bash
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly grvm="$root/target/debug/grvm"
readonly probe="$root/self-host-stage0/probes/g1_source_unit_artifact_write.glorious"

if [[ "${GRANDIOSE_GRVM_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-vm --bin grvm
fi

temporary="$(mktemp -d)"
trap 'rm -rf "$temporary"' EXIT
result="$(cd "$temporary" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$probe" GRANDIOSE_STAGE0_SERVICE_EXPECTED=132 \
    "$root/tooling/self-host-stage0-service-check.sh" \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic)"
[[ "$result" == "132" ]] || { echo "self-host G1 source-unit artifact check: source compilation failed: $result" >&2; exit 1; }
[[ "$(wc -c < "$temporary/source-unit.grbc")" == "944" ]] || { echo "self-host G1 source-unit artifact check: expected shifted canonical layout for the nine-byte entry name" >&2; exit 1; }
"$grvm" verify "$temporary/source-unit.grbc"
"$grvm" run "$temporary/source-unit.grbc"
printf '%s\n' "$result"
