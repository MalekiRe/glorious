#!/usr/bin/env bash
# Render the production self-host module graph as one canonical source file.
#
# The native host has a one-file compiler boundary.  This helper owns the
# production closure passed to that boundary, so the native build, provenance,
# and future stage bootstrap all consume identical source bytes.  Test-only
# `self-host/src/probe` files are deliberately absent.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage:
  tooling/self-host-production-source.sh inputs
  tooling/self-host-production-source.sh materialize --output FILE [--grc FILE]

`inputs` prints the canonical primary source followed by its production module
segments, one absolute path per line. `materialize` uses the release bootstrap
compiler's `--emit monolithic-source` route to replace that exact distributed
bundle with its checked, canonical single-file representation. It never reads
the test-only self-host probe tree.
USAGE
    exit 2
}

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/.." && pwd -P)"
readonly source_root="$repo_root/self-host/src"

inputs() {
    printf '%s\n' \
        "$source_root/main.glorious" \
        "$source_root/frontend/frontend.glorious" \
        "$source_root/frontend/lexer/lexer.glorious" \
        "$source_root/frontend/lossless/lossless.glorious" \
        "$source_root/frontend/scanner/scanner.glorious" \
        "$source_root/frontend/headers/headers.glorious" \
        "$source_root/frontend/bodies/bodies.glorious" \
        "$source_root/frontend/resolution/resolution.glorious" \
        "$source_root/frontend/elaboration/elaboration.glorious" \
        "$source_root/backend/backend.glorious" \
        "$source_root/backend/artifact/artifact.glorious" \
        "$source_root/backend/lowering/lowering.glorious" \
        "$source_root/backend/emission/emission.glorious" \
        "$source_root/compiler/compiler.glorious" \
        "$source_root/diagnostics/diagnostics.glorious" \
        "$source_root/diagnostics/model/model.glorious" \
        "$source_root/diagnostics/source_errors/source_errors.glorious" \
        "$source_root/diagnostics/backend_errors/backend_errors.glorious"
}

validate_inputs() {
    local input
    while IFS= read -r input; do
        [[ -f "$input" ]] || { echo "self-host-production-source: missing production source: $input" >&2; exit 1; }
        case "$input" in
            "$source_root/probe"/*)
                echo "self-host-production-source: probe source escaped production closure: $input" >&2
                exit 1
                ;;
        esac
    done < <(inputs)
}

materialize() {
    local output= grc="${G1_GRC_BIN:-$repo_root/target/release/grc}"
    while (($#)); do
        case "$1" in
            --output) output=${2:?missing output path}; shift 2 ;;
            --grc) grc=${2:?missing compiler path}; shift 2 ;;
            -h|--help) usage ;;
            *) usage ;;
        esac
    done
    [[ -n "$output" ]] || usage
    validate_inputs
    if [[ ! -x "$grc" ]]; then
        [[ "$grc" == "$repo_root/target/release/grc" ]] || {
            echo "self-host-production-source: bootstrap compiler is not executable: $grc" >&2
            exit 2
        }
        # The helper is called by the snapshot-native route through an
        # absolute path.  Do not let Cargo inherit a caller's (possibly live
        # checkout) directory: the requested compiler lives in this helper's
        # repository and must be built there.
        (
            cd -- "$repo_root"
            "$repo_root/tooling/ram-gate.sh" cargo build --release -p grandiose --bin grc
        )
    fi
    [[ -x "$grc" ]] || { echo "self-host-production-source: bootstrap compiler was not built: $grc" >&2; exit 1; }

    local output_dir temporary primary
    output_dir=$(cd -- "$(dirname -- "$output")" && pwd -P) || {
        echo "self-host-production-source: output directory does not exist: $(dirname -- "$output")" >&2
        exit 2
    }
    output="$output_dir/$(basename -- "$output")"
    temporary=$(mktemp "$output_dir/.self-host-production-source.XXXXXX")
    trap 'rm -f -- "$temporary"' RETURN
    mapfile -t source_inputs < <(inputs)
    primary=${source_inputs[0]}
    "$grc" -O3 --emit monolithic-source -o "$temporary" "$primary" "${source_inputs[@]:1}"
    [[ -s "$temporary" ]] || { echo "self-host-production-source: compiler emitted empty source" >&2; exit 1; }
    mv -f -- "$temporary" "$output"
    trap - RETURN
    printf '%s\n' "$output"
}

case "${1:-}" in
    inputs)
        shift
        (($# == 0)) || usage
        validate_inputs
        inputs
        ;;
    materialize)
        shift
        materialize "$@"
        ;;
    *) usage ;;
esac
