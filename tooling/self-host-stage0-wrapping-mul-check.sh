#!/usr/bin/env bash
# Proves generic u64 wrapping multiplication is manifest-bound end-to-end.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support_wrapping_mul.glorious"
readonly probe="$root/self-host-stage0/probes/wrapping_mul.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi
output="$("$compiler" --root-package wrapping-mul-probe@0.1.0 \
    --source compiler_support@0.1.0 src/lib.glorious "$support" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add \
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul \
    --runtime-leaf int-checked-div crate __g1_int_checked_div \
    run "$probe")"
[[ "$output" == "2" ]] || { echo "self-host wrapping-mul check: expected u64 wrapping product 2, got $output" >&2; exit 1; }
printf '%s\n' "$output"
