#!/usr/bin/env bash
# Proves process argv remains an explicit runtime-host capability for the
# source compiler world; the same program must fail closed without it.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly compiler="$root/target/debug/grc-stage0"
readonly support="$root/self-host-stage0/runtime/compiler_support.glorious"
readonly probe="$root/self-host-stage0/probes/process_args.glorious"

if [[ "${GRANDIOSE_STAGE0_ALREADY_BUILT:-0}" != 1 ]]; then
    cargo build -q -p grandiose-stage0 --bin grc-stage0
fi

run_probe() {
    "$compiler" \
        --root-package process-args-probe@0.1.0 \
        --source compiler_support@0.1.0 src/lib.glorious "$support" \
        --runtime-standard-library compiler_support@0.1.0 \
        --runtime-leaf branch-bool crate branch_bool \
        --runtime-leaf blake3 crate __g1_blake3 \
        --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
        --runtime-leaf text-eq crate __g1_text_eq \
        --runtime-leaf bytes-len crate __g1_bytes_len \
        --runtime-leaf bytes-get crate __g1_bytes_get \
        --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
        --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add \
        --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub \
        --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul \
        --runtime-leaf int-checked-div crate __g1_int_checked_div \
        --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len --runtime-leaf array-get-move crate __g1_array_get_move \
        --runtime-leaf array-pop-move crate __g1_array_pop_move \
        --runtime-host process_args __g1_process_args_get crate process_args_get \
        --capability process_args \
        run "$probe"
}

[[ "$(run_probe)" == "7" ]] || {
    echo "self-host process-args check: expected explicit argv host result" >&2
    exit 1
}

unbound_output="$("$compiler" --root-package process-args-probe@0.1.0 \
    --source compiler_support@0.1.0 src/lib.glorious "$support" \
    --runtime-standard-library compiler_support@0.1.0 \
    --runtime-leaf branch-bool crate branch_bool \
    --runtime-leaf blake3 crate __g1_blake3 \
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes \
    --runtime-leaf text-eq crate __g1_text_eq \
    --runtime-leaf bytes-len crate __g1_bytes_len \
    --runtime-leaf bytes-get crate __g1_bytes_get \
    --runtime-leaf bytes-slice crate __g1_bytes_slice --runtime-leaf bytes-concat crate __g1_bytes_concat --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move --runtime-leaf int-shr crate __g1_int_shr --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32 --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64 --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8 --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64 \
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add \
    --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub \
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul \
    --runtime-leaf int-checked-div crate __g1_int_checked_div \
    --runtime-leaf array-empty crate __g1_array_empty --runtime-leaf array-len crate __g1_array_len --runtime-leaf array-get-move crate __g1_array_get_move \
    --runtime-leaf array-pop-move crate __g1_array_pop_move \
    run "$probe")"
if [[ "$unbound_output" == "7" ]]; then
    echo "self-host process-args check: argv host call unexpectedly produced process arguments without authority" >&2
    exit 1
fi
