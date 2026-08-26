#!/usr/bin/env bash
# Exercises the production source-file -> compiler service -> atomic output
# route. The independently implemented Rust VM remains the verifier/runtime.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly grvm="$root/target/debug/grvm"
readonly probe="$root/self-host-stage0/probes/g1_file_unit_artifact_write.glorious"

if [[ "${GRANDIOSE_GRVM_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-vm --bin grvm
fi

temporary="$(mktemp -d)"
trap 'rm -rf "$temporary"' EXIT
printf '%s\n' 'pub fn boot() -> Unit { () }' > "$temporary/unit-entry-input.glorious"
printf '%s\n' 'pub fn answer() -> i64 { 40 + 2 }' > "$temporary/arithmetic-input.glorious"
result="$(cd "$temporary" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$probe" GRANDIOSE_STAGE0_SERVICE_EXPECTED=140 \
    "$root/tooling/self-host-stage0-service-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic)"
[[ "$result" == "140" ]] || { echo "self-host G1 file-unit artifact check: source compilation failed: $result" >&2; exit 1; }
[[ "$(wc -c < "$temporary/unit-entry-output.grbc")" == "936" ]] || { echo "self-host G1 file-unit artifact check: expected 936 bytes" >&2; exit 1; }
"$grvm" verify "$temporary/unit-entry-output.grbc"
"$grvm" run "$temporary/unit-entry-output.grbc"
[[ "$(wc -c < "$temporary/arithmetic-output.grbc")" == "1280" ]] || { echo "self-host G1 file-unit artifact check: expected 1280 arithmetic bytes" >&2; exit 1; }
"$grvm" verify "$temporary/arithmetic-output.grbc"
"$grvm" run "$temporary/arithmetic-output.grbc"

# Rejection is just as important as the happy path: invalid source must not
# consume the publication capability or leave an artifact behind.
invalid="$temporary/invalid"
mkdir "$invalid"
printf '%s\n' 'pub fn boot() -> Unit { 1 }' > "$invalid/unit-entry-input.glorious"
invalid_result="$(cd "$invalid" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$probe" GRANDIOSE_STAGE0_SERVICE_EXPECTED=0 \
    "$root/tooling/self-host-stage0-service-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic)"
[[ "$invalid_result" == "0" ]] || { echo "self-host G1 file-unit artifact check: malformed source was accepted: $invalid_result" >&2; exit 1; }
[[ ! -e "$invalid/unit-entry-output.grbc" ]] || { echo "self-host G1 file-unit artifact check: rejected source published an artifact" >&2; exit 1; }
printf '%s\n' "$result"
