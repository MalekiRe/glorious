#!/usr/bin/env bash
# Strict front door for the future .grbc -> LLVM/native backend.
#
# The bootstrap compiler can already turn *source* into O3/Wild executables,
# This driver keeps the artifact boundary explicit: it verifies the artifact
# with grvm, asks release `grc` to lower only its supported verified AOT slice
# to LLVM, and asks clang to compile that IR at O3 through Wild. It never
# invokes `grvm run`, so VM execution cannot be mistaken for a native stage.
set -euo pipefail

usage() {
    cat >&2 <<'USAGE'
usage: tooling/grbc-native.sh --artifact FILE --output FILE [--grvm FILE] [--grc FILE]

Lowers the supported verified G1 bytecode artifact subset to an O3/Wild native
executable. Unsupported artifacts fail closed; this script never runs bytecode.
USAGE
    exit 2
}

readonly script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly repo_root="$(cd -- "$script_dir/.." && pwd -P)"
readonly native_host_runtime="$repo_root/crates/grandiose/src/native_host_runtime.c"
artifact=
output=
grvm="$repo_root/target/release/grvm"
grc="$repo_root/target/release/grc"

while (($#)); do
    case "$1" in
        --artifact) artifact=${2:?missing value}; shift 2 ;;
        --output) output=${2:?missing value}; shift 2 ;;
        --grvm) grvm=${2:?missing value}; shift 2 ;;
        --grc) grc=${2:?missing value}; shift 2 ;;
        -h|--help) usage ;;
        *) usage ;;
    esac
done

[[ -n "$artifact" && -n "$output" ]] || usage
[[ -f "$artifact" ]] || { echo "grbc-native: artifact is missing: $artifact" >&2; exit 2; }
# `-e` is false for a dangling symlink, while clang would follow that symlink
# and create (or overwrite) its target. Treat every existing directory entry
# as occupied so this boundary never writes through a caller-provided link.
[[ ! -e "$output" && ! -L "$output" ]] || { echo "grbc-native: refusing to overwrite output: $output" >&2; exit 2; }
[[ -x "$grvm" ]] || { echo "grbc-native: release grvm is missing: $grvm" >&2; exit 2; }
[[ -x "$grc" ]] || { echo "grbc-native: release grc is missing: $grc" >&2; exit 2; }
command -v clang >/dev/null || { echo "grbc-native: clang is required for O3 LLVM compilation" >&2; exit 2; }
command -v wild >/dev/null || { echo "grbc-native: Wild linker is required for native output" >&2; exit 2; }
[[ -f "$native_host_runtime" ]] || { echo "grbc-native: bundled native host runtime is missing: $native_host_runtime" >&2; exit 2; }

# This subcommand decodes and verifies only. It does not run bytecode.
"$grvm" native-preflight "$artifact"

artifact_ir="$(mktemp "${TMPDIR:-/tmp}/grbc-native.XXXXXX.ll")"
trap 'rm -f -- "$artifact_ir"' EXIT

# `grc --artifact-llvm-ir` is a decode+verify+lower operation. It has no
# source compiler fallback and reports unsupported bytecode as an error.
"$grc" --artifact-llvm-ir "$artifact" -o "$artifact_ir"

# Feed exactly the emitted artifact IR plus the bundled, finite host ABI to
# clang.  `native_host_runtime.c` supplies only the frozen process/fs/
# diagnostic import symbols; it is not a VM or a fallback execution path.
# --ld-path makes Wild the final linker, while -O3 is deliberately fixed for
# stage convergence.
clang -x ir -O3 --ld-path=wild "$artifact_ir" -x c "$native_host_runtime" -o "$output"
[[ -x "$output" ]] || {
    echo "grbc-native: clang reported success but produced no executable: $output" >&2
    exit 1
}
