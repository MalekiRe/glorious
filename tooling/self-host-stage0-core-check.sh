#!/usr/bin/env bash
# Executes M20 body-to-Core type admission in source.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/core.glorious"
readonly library="$root/self-host-stage0/probes/core_library.glorious"
readonly identity="$root/self-host-stage0/src/identity/identity.glorious"
readonly source="$root/self-host-stage0/src/source/source.glorious"
readonly scanner="$root/self-host-stage0/src/scanner/scanner.glorious"
readonly types="$root/self-host-stage0/src/types/types.glorious"
readonly signature="$root/self-host-stage0/src/signature/signature.glorious"
readonly pattern="$root/self-host-stage0/src/pattern/pattern.glorious"
readonly placeflow="$root/self-host-stage0/src/placeflow/placeflow.glorious"
readonly body="$root/self-host-stage0/src/body/body.glorious"
readonly core="$root/self-host-stage0/src/core/core.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi

output="$("$compiler" \
    --root-package core-probe@0.1.0 \
    --source compiler_support@0.1.0 src/lib.glorious "$support" \
    --source core-library@0.1.0 src/lib.glorious "$library" \
    --source core-library@0.1.0 src/identity/identity.glorious "$identity" \
    --source core-library@0.1.0 src/source/source.glorious "$source" \
    --source core-library@0.1.0 src/scanner/scanner.glorious "$scanner" \
    --source core-library@0.1.0 src/types/types.glorious "$types" \
    --source core-library@0.1.0 src/signature/signature.glorious "$signature" \
    --source core-library@0.1.0 src/pattern/pattern.glorious "$pattern" \
    --source core-library@0.1.0 src/placeflow/placeflow.glorious "$placeflow" \
    --source core-library@0.1.0 src/body/body.glorious "$body" \
    --source core-library@0.1.0 src/core/core.glorious "$core" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice \
    --runtime-leaf bytes-concat crate __g1_bytes_concat \
    --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move \
    --runtime-leaf int-shr crate __g1_int_shr \
    --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 \
    --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 \
    --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 \
    --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add \
    --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub \
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul \
    --runtime-leaf int-checked-div crate __g1_int_checked_div \
    --runtime-leaf array-empty crate __g1_array_empty \
    --runtime-leaf array-len crate __g1_array_len \
    --runtime-leaf array-get-move crate __g1_array_get_move \
    --runtime-leaf array-pop-move crate __g1_array_pop_move \
    run "$probe")"

[[ "$output" == "30" ]] || {
    echo "self-host core check: expected scalar, bound parameter forms, closure-capture kind, typed unsigned literal/arithmetic payloads, call, pattern-test kind, scalar operands, callable contracts, and Body-owned source syntax category admission/rejection, got $output" >&2
    exit 1
}
printf '%s\n' "$output"
