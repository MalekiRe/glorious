#!/usr/bin/env bash
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/vm-backend.glorious"
readonly library="$root/self-host-stage0/probes/vm_backend_library.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi

source_args=(
    --source compiler_support@0.1.0 src/lib.glorious "$support"
    --source vm-backend-library@0.1.0 src/lib.glorious "$library"
)
for module in bootstrap_indirection identity types signature pattern body core mir_storage mir runtime_manifest vm_backend; do
    source_args+=(--source vm-backend-library@0.1.0 "src/$module/$module.glorious" "$root/self-host-stage0/src/$module/$module.glorious")
done

output="$(timeout --kill-after=5s --preserve-status 120s "$compiler" --root-package vm-backend-probe@0.1.0 "${source_args[@]}" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-leaf branch-bool crate branch_bool --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat \
    --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move \
    --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub \
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul --runtime-leaf int-checked-div crate __g1_int_checked_div \
    --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len \
    --runtime-leaf array-get-move crate __g1_array_get_move --runtime-leaf array-pop-move crate __g1_array_pop_move \
    run "$probe")"

[[ "$output" == "576" ]] || {
    echo "self-host vm backend check: expected canonical G1 schema admission, magic/header, manifest-bound imports, and verified execution paths, got $output" >&2
    exit 1
}
printf '%s\n' "$output"
