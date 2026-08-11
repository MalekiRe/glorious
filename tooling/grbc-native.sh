#!/usr/bin/env bash
# Strict front door for the future .grbc -> LLVM/native backend.
#
# The bootstrap compiler can already turn *source* into O3/Wild executables,
# but it cannot yet lower a decoded bytecode artifact to LLVM.  This driver
# makes that missing boundary explicit: it verifies the artifact with grvm,
# requires the intended O3/Wild native toolchain, and then refuses to emit an
# executable. In particular it never invokes `grvm run`, so no VM execution
# can be mistaken for a native compiler stage.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/grbc-native.sh --artifact FILE --output FILE [--grvm FILE]

Preflights FILE as a verified G1 bytecode artifact for the future O3/Wild
artifact-to-native backend. No executable is emitted until that backend exists.
USAGE
    exit 2
}

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/.." && pwd -P)"
artifact=
output=
grvm="$repo_root/target/release/grvm"

while (($#)); do
    case "$1" in
        --artifact) artifact=${2:?missing value}; shift 2 ;;
        --output) output=${2:?missing value}; shift 2 ;;
        --grvm) grvm=${2:?missing value}; shift 2 ;;
        -h|--help) usage ;;
        *) usage ;;
    esac
done

[[ -n "$artifact" && -n "$output" ]] || usage
[[ -f "$artifact" ]] || { echo "grbc-native: artifact is missing: $artifact" >&2; exit 2; }
[[ ! -e "$output" ]] || { echo "grbc-native: refusing to overwrite output: $output" >&2; exit 2; }
[[ -x "$grvm" ]] || { echo "grbc-native: release grvm is missing: $grvm" >&2; exit 2; }
command -v clang >/dev/null || { echo "grbc-native: clang is required for O3 LLVM compilation" >&2; exit 2; }
command -v wild >/dev/null || { echo "grbc-native: Wild linker is required for native output" >&2; exit 2; }

# This subcommand decodes and verifies only. It does not run bytecode.
"$grvm" native-preflight "$artifact"

echo "grbc-native: verified artifact-to-native lowering is not implemented; no native output was produced" >&2
exit 1
