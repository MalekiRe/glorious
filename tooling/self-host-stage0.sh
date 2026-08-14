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

(cd "$repo_root" && cargo build -q -p grandiose-stage0 --bin grc-stage0)
stage0="$repo_root/target/debug/grc-stage0"

runtime_manifest=(
    --runtime-standard-library command@0.1.0
    --runtime-leaf text-byte-len crate __g1_text_byte_len
    --runtime-leaf text-concat crate __g1_text_concat
    --runtime-leaf text-eq crate __g1_text_eq
    --runtime-leaf text-from-utf8-checked crate __g1_text_from_utf8_checked
    --runtime-leaf text-as-bytes crate __g1_text_as_bytes
)

case "$mode" in
    check)
        "$stage0" "${runtime_manifest[@]}" check "$canonical_source"
        ;;
    emit)
        "$stage0" "${runtime_manifest[@]}" emit-bootstrap-vm \
            "$canonical_source" "$artifact" "$manifest"
        ;;
esac
