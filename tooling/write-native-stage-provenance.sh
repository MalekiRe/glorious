#!/usr/bin/env bash
# Write an immutable provenance manifest for an O3/Wild native compiler stage.
#
# This helper does not itself compile a .grbc artifact. `grbc-native.sh` owns
# that verified, fail-closed lowering boundary; this helper binds the exact
# executable it produced to the exact .grbc it represents.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/write-native-stage-provenance.sh \
  --stage 1|2 --native FILE --source FILE --output FILE \
  [--compiler-bytecode FILE]

Writes a new TSV provenance file atomically. All stages must be O3, Wild-linked
native executables. Stage 2 additionally requires --compiler-bytecode; its
SHA-256 is recorded so the convergence checker rejects a stale or unrelated
native host. Existing output files are never overwritten.
USAGE
    exit 2
}

stage=
native=
source_file=
output=
compiler_bytecode=
while (($#)); do
    case "$1" in
        --stage) stage=${2:?missing value}; shift 2 ;;
        --native) native=${2:?missing value}; shift 2 ;;
        --source) source_file=${2:?missing value}; shift 2 ;;
        --output) output=${2:?missing value}; shift 2 ;;
        --compiler-bytecode) compiler_bytecode=${2:?missing value}; shift 2 ;;
        -h|--help) usage ;;
        *) usage ;;
    esac
done

[[ "$stage" == 1 || "$stage" == 2 ]] || { echo "native-stage-provenance: --stage must be 1 or 2" >&2; exit 2; }
[[ -x "$native" ]] || { echo "native-stage-provenance: native executable is missing: $native" >&2; exit 2; }
[[ -f "$source_file" ]] || { echo "native-stage-provenance: source is missing: $source_file" >&2; exit 2; }
[[ ! -e "$output" ]] || { echo "native-stage-provenance: refusing to overwrite existing evidence: $output" >&2; exit 2; }
if [[ "$stage" == 1 ]]; then
    [[ -z "$compiler_bytecode" ]] || { echo "native-stage-provenance: stage 1 must not claim a compiler-bytecode artifact" >&2; exit 2; }
else
    [[ -n "$compiler_bytecode" && -s "$compiler_bytecode" ]] || {
        echo "native-stage-provenance: stage 2 requires a nonempty --compiler-bytecode artifact" >&2
        exit 2
    }
fi

readelf -p .comment "$native" 2>/dev/null | grep -Eqi 'wild' || {
    echo "native-stage-provenance: executable lacks a Wild linker marker in .comment: $native" >&2
    exit 1
}

output_dir=$(dirname -- "$output")
mkdir -p "$output_dir"
temporary=$(mktemp "$output_dir/.${output##*/}.tmp.XXXXXX")
trap 'rm -f -- "$temporary"' EXIT
{
    printf 'schema\t1\n'
    printf 'stage\t%s\n' "$stage"
    printf 'optimization\tO3\n'
    printf 'linker\twild\n'
    printf 'native-sha256\t%s\n' "$(sha256sum "$native" | awk '{print $1}')"
    printf 'source-sha256\t%s\n' "$(sha256sum "$source_file" | awk '{print $1}')"
    if [[ "$stage" == 2 ]]; then
        printf 'compiler-bytecode-sha256\t%s\n' "$(sha256sum "$compiler_bytecode" | awk '{print $1}')"
    fi
} > "$temporary"
ln -- "$temporary" "$output" || {
    echo "native-stage-provenance: output appeared while publishing; retained existing evidence: $output" >&2
    exit 1
}
rm -f -- "$temporary"
trap - EXIT
printf '%s\n' "$output"
