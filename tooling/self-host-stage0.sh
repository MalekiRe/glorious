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
artifact and its bound bootstrap manifest. No ambient source files or runtime
capabilities are supplied to the compiler service.
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
(cd "$repo_root" && cargo build -q -p grandiose-stage0 --bin grc-stage0)
stage0="$stage0_target/debug/grc-stage0"

runtime_manifest=(
    --runtime-standard-library command@0.1.0
    --runtime-leaf text-byte-len crate __g1_text_byte_len
    --runtime-leaf text-concat crate __g1_text_concat
    --runtime-leaf text-eq crate __g1_text_eq
    --runtime-leaf text-from-utf8-checked crate __g1_text_from_utf8_checked
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes
    --runtime-leaf int-checked-add crate __g1_int_checked_add
    --runtime-leaf int-wrapping-add crate __g1_int_wrapping_add
    --runtime-leaf int-wrapping-sub crate __g1_int_wrapping_sub
    --runtime-leaf int-wrapping-mul crate __g1_int_wrapping_mul
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
)

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
