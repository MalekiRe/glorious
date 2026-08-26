#!/usr/bin/env bash
# Proves source-owned verify-vm argv dispatch reaches the bounded G1 artifact
# verifier. A canonical source-emitted artifact is accepted; malformed argv
# and arbitrary bytes are rejected before any result can be reported valid.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
temporary="$(mktemp -d)"
trap 'rm -rf "$temporary"' EXIT

printf '%s\n' 'pub fn answer() -> i64 { 40 + 2 }' > "$temporary/arithmetic-input.glorious"
printf '%s\n' 'pub fn select() -> i64 { if false { 7 } else { 9 } }' > "$temporary/select-input.glorious"

# Use the source compiler's existing publication route to obtain the G1
# image. This avoids treating the normal compiler's distinct artifact format
# as evidence for the source verifier.
emit_result="$(cd "$temporary" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/g1_cli_emit_vm_file_artifact_write.glorious" GRANDIOSE_STAGE0_SERVICE_EXPECTED=135 \
    "$root/tooling/self-host-stage0-service-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic)"
[[ "$emit_result" == "135" ]] || { echo "self-host G1 CLI verify-vm check: cannot produce source artifact: $emit_result" >&2; exit 1; }
mv "$temporary/arithmetic-output.grbc" "$temporary/valid.grbc"
printf '%s\n' 'not a G1 artifact' > "$temporary/invalid.grbc"

result="$(cd "$temporary" && GRANDIOSE_STAGE0_ALREADY_BUILT=1 GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/g1_cli_verify_vm_file.glorious" GRANDIOSE_STAGE0_SERVICE_EXPECTED=137 \
    "$root/tooling/self-host-stage0-service-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file --capability file_read)"
[[ "$result" == "137" ]] || { echo "self-host G1 CLI verify-vm check: source verification dispatch failed: $result" >&2; exit 1; }
printf '%s\n' "$result"
