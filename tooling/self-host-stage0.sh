#!/usr/bin/env bash
# Materialize the canonical self-host compiler and drive the independent Rust
# Stage-0 bootstrap boundary. The released `grc` seed is used only to render
# the canonical source bundle; Stage-0 owns parsing, semantic checking, VM
# emission, verification, and bootstrap-manifest production.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage:
  tooling/self-host-stage0.sh check [--seed GRC]
  tooling/self-host-stage0.sh emit --artifact PROGRAM --manifest MANIFEST [--seed GRC]

`check` verifies the canonical self-host source under the exact supported
Stage-0 runtime manifest. `emit` additionally writes a verified stage-one VM
artifact and its bound bootstrap manifest. All source files, primitive leaves,
and the four frozen host capabilities are explicitly supplied to the compiler
service; no ambient authority is used.
USAGE
    exit 2
}

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/.." && pwd -P)"

[[ $# -ge 1 ]] || usage
mode="$1"
shift
seed="$repo_root/target/release/grc"
artifact=""
manifest=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --seed)
            [[ $# -ge 2 ]] || usage
            seed="$2"
            shift 2
            ;;
        --artifact)
            [[ $# -ge 2 ]] || usage
            artifact="$2"
            shift 2
            ;;
        --manifest)
            [[ $# -ge 2 ]] || usage
            manifest="$2"
            shift 2
            ;;
        *) usage ;;
    esac
done

case "$mode" in
    check)
        [[ -z "$artifact" && -z "$manifest" ]] || usage
        ;;
    emit)
        [[ -n "$artifact" && -n "$manifest" ]] || usage
        ;;
    *) usage ;;
esac

[[ -x "$seed" ]] || {
    echo "self-host-stage0: released seed is not executable: $seed" >&2
    exit 1
}

temporary_directory="$(mktemp -d /tmp/grandiose-self-host-stage0.XXXXXX)"
trap 'rm -rf "$temporary_directory"' EXIT
canonical_source="$temporary_directory/compiler.glorious"

"$repo_root/tooling/self-host-production-source.sh" materialize \
    --output "$canonical_source" \
    --grc "$seed"

# Honor an explicitly isolated Cargo target directory. This keeps the
# hermetic regression usable in constrained CI/worktree environments without
# silently rebuilding into a caller's checkout-local `target` tree.
stage0_target="${CARGO_TARGET_DIR:-$repo_root/target}"
(cd "$repo_root" && cargo build -q --release -p grandiose-stage0 --bin grc-stage0)
stage0="$stage0_target/release/grc-stage0"

runtime_manifest=(
    --capability process_args
    --capability file_read
    --capability file_write
    --capability diagnostic
    --runtime-standard-library command@0.1.0
    --runtime-leaf abort crate __g1_abort
    --runtime-leaf text-byte-len crate __g1_text_byte_len
    --runtime-leaf text-concat crate __g1_text_concat
    --runtime-leaf text-eq crate __g1_text_eq
    --runtime-leaf text-from-utf8-checked crate __g1_text_from_utf8_checked
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes
    --runtime-leaf bytes-len crate __g1_bytes_len
    --runtime-leaf bytes-concat crate __g1_bytes_concat
    --runtime-leaf bytes-get crate __g1_bytes_get
    --runtime-leaf bytes-slice crate __g1_bytes_slice
    --runtime-leaf bytes-from-array-move crate __g1_bytes_from_array_move
    --runtime-leaf bytes-to-array crate __g1_bytes_to_array
    --runtime-leaf bytes-utf8-valid-up-to crate __g1_bytes_utf8_valid_up_to
    --runtime-leaf array-new crate __g1_array_new
    --runtime-leaf array-len crate __g1_array_len
    --runtime-leaf array-get-copy crate __g1_array_get_copy
    --runtime-leaf array-get-move crate __g1_array_get_move
    --runtime-leaf array-get-borrow-shared crate __g1_array_get_borrow_shared
    --runtime-leaf array-get-borrow-unique crate __g1_array_get_borrow_unique
    --runtime-leaf array-set-move crate __g1_array_set_move
    --runtime-leaf array-empty crate __g1_array_empty
    --runtime-leaf array-push-move crate __g1_array_push_move
    --runtime-leaf array-pop-move crate __g1_array_pop_move
    --runtime-leaf array-capacity crate __g1_array_capacity
    --runtime-leaf array-reserve crate __g1_array_reserve
    --runtime-leaf array-finish-drained crate __g1_array_finish_drained
    --runtime-leaf char-from-u32-checked crate __g1_char_from_u32_checked
    --runtime-leaf char-to-u32 crate __g1_char_to_u32
    --runtime-leaf int-checked-add crate __g1_int_checked_add
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add
    --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul
    --runtime-leaf int-wrapping-neg crate __g1_int_wrapping_neg
    --runtime-leaf int-equal crate __g1_int_equal
    --runtime-leaf int-less crate __g1_int_less
    --runtime-leaf int-greater crate __g1_int_greater
    --runtime-leaf int-bit-and crate __g1_int_bit_and
    --runtime-leaf int-bit-or crate __g1_int_bit_or
    --runtime-leaf int-bit-xor crate __g1_int_bit_xor
    --runtime-leaf int-bit-not crate __g1_int_bit_not
    --runtime-leaf int-shr crate __g1_int_shr
    --runtime-leaf int-shl crate __g1_int_shl
    --runtime-leaf int-convert-checked-to-i64 crate __g1_int_convert_checked_to_i64
    --runtime-leaf int-convert-wrapping-to-i64 crate __g1_int_convert_wrapping_to_i64
    --runtime-leaf int-convert-checked-to-u32 crate __g1_int_convert_checked_to_u32
    --runtime-leaf int-convert-wrapping-to-u32 crate __g1_int_convert_wrapping_to_u32
    --runtime-leaf int-convert-checked-to-usize crate __g1_int_convert_checked_to_usize
    --runtime-leaf int-convert-wrapping-to-usize crate __g1_int_convert_wrapping_to_usize
    --runtime-leaf int-convert-checked-to-u8 crate __g1_int_convert_checked_to_u8
    --runtime-leaf int-convert-wrapping-to-u8 crate __g1_int_convert_wrapping_to_u8
    --runtime-leaf int-convert-checked-to-u16 crate __g1_int_convert_checked_to_u16
    --runtime-leaf int-convert-wrapping-to-u16 crate __g1_int_convert_wrapping_to_u16
    --runtime-leaf int-convert-checked-to-i16 crate __g1_int_convert_checked_to_i16
    --runtime-leaf int-convert-wrapping-to-i16 crate __g1_int_convert_wrapping_to_i16
    --runtime-leaf int-convert-checked-to-i32 crate __g1_int_convert_checked_to_i32
    --runtime-leaf int-convert-wrapping-to-i32 crate __g1_int_convert_wrapping_to_i32
    --runtime-leaf int-convert-checked-to-i8 crate __g1_int_convert_checked_to_i8
    --runtime-leaf int-convert-wrapping-to-i8 crate __g1_int_convert_wrapping_to_i8
    --runtime-leaf int-convert-checked-to-u64 crate __g1_int_convert_checked_to_u64
    --runtime-leaf int-convert-wrapping-to-u64 crate __g1_int_convert_wrapping_to_u64
    --runtime-leaf int-convert-checked-to-isize crate __g1_int_convert_checked_to_isize
    --runtime-leaf int-convert-wrapping-to-isize crate __g1_int_convert_wrapping_to_isize
    --runtime-leaf int-convert-checked-to-u128 crate __g1_int_convert_checked_to_u128
    --runtime-leaf int-convert-wrapping-to-u128 crate __g1_int_convert_wrapping_to_u128
    --runtime-leaf int-convert-checked-to-i128 crate __g1_int_convert_checked_to_i128
    --runtime-leaf int-convert-wrapping-to-i128 crate __g1_int_convert_wrapping_to_i128
)

# The canonical runtime's floating leaves are all trusted opaque boundaries.
# Construct this finite table rather than hand-maintaining nearly eighty
# repeated entries; the selector parser validates every generated role and
# each still binds one exact declaration identity.
for float_width in f32 f64; do
    for float_op in add sub mul div rem neg eq ne lt le gt ge; do
        runtime_manifest+=(
            "--runtime-leaf" "${float_width}-${float_op}" crate "__g1_${float_width}_${float_op}"
        )
    done
    runtime_manifest+=(
        "--runtime-leaf" "${float_width}-to-bits" crate "__g1_${float_width}_to_bits"
        "--runtime-leaf" "${float_width}-from-bits" crate "__g1_${float_width}_from_bits"
    )
done
runtime_manifest+=(
    "--runtime-leaf" f32-to-f64 crate __g1_f32_to_f64
    "--runtime-leaf" f64-to-f32 crate __g1_f64_to_f32
)
for integer_width in u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize; do
    for float_width in f32 f64; do
        runtime_manifest+=(
            "--runtime-leaf" "${integer_width}-to-${float_width}" crate "__g1_${integer_width}_to_${float_width}"
            "--runtime-leaf" "${float_width}-to-${integer_width}-checked" crate "__g1_${float_width}_to_${integer_width}_checked"
        )
    done
done

case "$mode" in
    check)
        "$stage0" "${runtime_manifest[@]}" check "$canonical_source"
        ;;
    emit)
        "$stage0" "${runtime_manifest[@]}" emit-bootstrap-vm \
            "$canonical_source" "$artifact" "$manifest"
        # Do not trust the emitting invocation to validate its own output.
        # The program has crossed a file boundary here, so verify the exact
        # serialized bytes independently before treating this bootstrap edge
        # as publishable.
        "$stage0" verify-vm "$artifact"

        # Also prove that the manifest is actually bound to this artifact.
        # Supplying a deliberately damaged adjacent manifest must fail before
        # convergence comparison; accepting it would make a green `emit`
        # result insufficient evidence for the stage-one bootstrap edge.
        invalid_manifest="$temporary_directory/invalid-adjacent.manifest"
        cp -- "$manifest" "$invalid_manifest"
        printf '\0' >> "$invalid_manifest"
        if "$stage0" verify-bootstrap \
            "$artifact" "$manifest" "$artifact" "$invalid_manifest" \
            >/dev/null 2>&1; then
            echo "self-host-stage0: bootstrap verification accepted a corrupted adjacent manifest" >&2
            exit 1
        fi
        ;;
esac
