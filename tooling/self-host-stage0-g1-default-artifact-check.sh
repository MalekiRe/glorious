#!/usr/bin/env bash
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly grvm="$root/target/debug/grvm"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/g1_default_artifact_write.glorious"
readonly library="$root/self-host-stage0/probes/vm_backend_library.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi
if [[ "${GRANDIOSE_GRVM_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-vm --bin grvm
fi

temporary="$(mktemp -d)"
trap 'rm -rf "$temporary"' EXIT
source_args=(--source compiler_support@0.1.0 src/lib.glorious "$support" --source g1-artifact-library@0.1.0 src/lib.glorious "$library")
for module in bootstrap_indirection identity types signature pattern body core mir_storage mir runtime_manifest vm_backend; do
    source_args+=(--source g1-artifact-library@0.1.0 "src/$module/$module.glorious" "$root/self-host-stage0/src/$module/$module.glorious")
done

result="$(cd "$temporary" && "$compiler" --root-package g1-default-artifact@0.1.0 "${source_args[@]}" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-host file_write_atomic __g1_fs_write_atomic crate write_file_atomically --capability file_write_atomic \
    --runtime-leaf branch-bool crate branch_bool --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat \
    --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move \
    --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub \
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul --runtime-leaf int-checked-div crate __g1_int_checked_div \
    --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len \
    --runtime-leaf array-get-move crate __g1_array_get_move --runtime-leaf array-pop-move crate __g1_array_pop_move run "$probe")"
[[ "$result" == "131" ]] || { echo "self-host G1 default artifact check: source write failed: $result" >&2; exit 1; }
[[ "$(wc -c < "$temporary/default.grbc")" == "936" ]] || {
    echo "self-host G1 default artifact check: expected 936 source-produced bytes, got $(wc -c < "$temporary/default.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/minimal.grbc")" == "808" ]] || {
    echo "self-host G1 default artifact check: expected 808 source-produced minimal-library bytes, got $(wc -c < "$temporary/minimal.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/i64.grbc")" == "1008" ]] || {
    echo "self-host G1 default artifact check: expected 1008 source-produced i64 bytes, got $(wc -c < "$temporary/i64.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/i64-negative.grbc")" == "1008" ]] || {
    echo "self-host G1 default artifact check: expected 1008 source-produced negative-i64 bytes, got $(wc -c < "$temporary/i64-negative.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/i64-callable.grbc")" == "1168" ]] || {
    echo "self-host G1 default artifact check: expected 1168 source-produced i64-callable bytes, got $(wc -c < "$temporary/i64-callable.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/i64-callable-negative.grbc")" == "1168" ]] || {
    echo "self-host G1 default artifact check: expected 1168 source-produced negative-i64-callable bytes, got $(wc -c < "$temporary/i64-callable-negative.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/i64-add.grbc")" == "1280" ]] || {
    echo "self-host G1 default artifact check: expected 1280 source-produced i64-add bytes, got $(wc -c < "$temporary/i64-add.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/i64-add-reversed.grbc")" == "1280" ]] || {
    echo "self-host G1 default artifact check: expected 1280 source-produced reversed-i64-add bytes, got $(wc -c < "$temporary/i64-add-reversed.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/i64-add-duplicate.grbc")" == "1264" ]] || {
    echo "self-host G1 default artifact check: expected 1264 source-produced duplicate-i64-add bytes, got $(wc -c < "$temporary/i64-add-duplicate.grbc")" >&2
    exit 1
}
for primitive_artifact in i64-subtract.grbc i64-multiply.grbc i64-divide.grbc; do
    [[ "$(wc -c < "$temporary/$primitive_artifact")" == "1280" ]] || {
        echo "self-host G1 default artifact check: expected 1280 source-produced $primitive_artifact bytes, got $(wc -c < "$temporary/$primitive_artifact")" >&2
        exit 1
    }
done
[[ "$(wc -c < "$temporary/i64-identity-call.grbc")" == "1176" ]] || {
    echo "self-host G1 default artifact check: expected 1176 source-produced i64 identity-call bytes, got $(wc -c < "$temporary/i64-identity-call.grbc")" >&2
    exit 1
}
[[ "$(wc -c < "$temporary/i64-binary-call.grbc")" == "1288" ]] || {
    echo "self-host G1 default artifact check: expected 1288 source-produced i64 binary-call bytes, got $(wc -c < "$temporary/i64-binary-call.grbc")" >&2
    exit 1
}
for binary_call_artifact in i64-binary-call-subtract.grbc i64-binary-call-multiply.grbc i64-binary-call-divide.grbc; do
    [[ "$(wc -c < "$temporary/$binary_call_artifact")" == "1288" ]] || {
        echo "self-host G1 default artifact check: expected 1288 source-produced $binary_call_artifact bytes, got $(wc -c < "$temporary/$binary_call_artifact")" >&2
        exit 1
    }
done
"$grvm" verify "$temporary/default.grbc"
"$grvm" verify "$temporary/minimal.grbc"
"$grvm" verify "$temporary/i64.grbc"
"$grvm" verify "$temporary/i64-negative.grbc"
"$grvm" verify "$temporary/i64-callable.grbc"
"$grvm" verify "$temporary/i64-callable-negative.grbc"
"$grvm" verify "$temporary/i64-add.grbc"
"$grvm" verify "$temporary/i64-add-reversed.grbc"
"$grvm" verify "$temporary/i64-add-duplicate.grbc"
"$grvm" verify "$temporary/i64-subtract.grbc"
"$grvm" verify "$temporary/i64-multiply.grbc"
"$grvm" verify "$temporary/i64-divide.grbc"
"$grvm" verify "$temporary/i64-identity-call.grbc"
"$grvm" verify "$temporary/i64-binary-call.grbc"
"$grvm" verify "$temporary/i64-binary-call-subtract.grbc"
"$grvm" verify "$temporary/i64-binary-call-multiply.grbc"
"$grvm" verify "$temporary/i64-binary-call-divide.grbc"
"$grvm" run "$temporary/default.grbc"
"$grvm" run "$temporary/i64.grbc"
"$grvm" run "$temporary/i64-negative.grbc"
"$grvm" run "$temporary/i64-callable.grbc"
"$grvm" run "$temporary/i64-callable-negative.grbc"
"$grvm" run "$temporary/i64-add.grbc"
"$grvm" run "$temporary/i64-add-reversed.grbc"
"$grvm" run "$temporary/i64-add-duplicate.grbc"
"$grvm" run "$temporary/i64-subtract.grbc"
"$grvm" run "$temporary/i64-multiply.grbc"
"$grvm" run "$temporary/i64-divide.grbc"
"$grvm" run "$temporary/i64-identity-call.grbc"
"$grvm" run "$temporary/i64-binary-call.grbc"
"$grvm" run "$temporary/i64-binary-call-subtract.grbc"
"$grvm" run "$temporary/i64-binary-call-multiply.grbc"
"$grvm" run "$temporary/i64-binary-call-divide.grbc"
printf '%s\n' "$result"
