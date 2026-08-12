#!/usr/bin/env bash
# Build and run the current self-host compiler through the native LLVM path.
#
# This is deliberately a development probe, not part of bootstrap convergence:
# it always emits a native executable with Wild and never substitutes the VM.
set -euo pipefail

usage() {
    cat <<'EOF'
usage: tooling/native-selfhost.sh [--rebuild] <output.grbc> <input.glorious>

Builds self-host/src/main.glorious with the release bootstrap compiler at -O3,
links the native executable through Wild, and invokes that executable with OUTPUT and INPUT.

Environment:
  G1_NATIVE_SELFHOST_CACHE_DIR  private cache directory (default: target/native-selfhost)
  G1_NATIVE_SELFHOST_SEED_DIR   read-only known-good cache to copy into a new worktree
  G1_GRC_BIN                    release grc binary to use instead of building one

The seed is copied only when the private cache is first created. The runner never
writes a seed or any cache belonging to another worktree.
EOF
}

rebuild=0
if [[ ${1:-} == -h || ${1:-} == --help ]]; then
    usage
    exit 0
fi
if [[ ${1:-} == --rebuild ]]; then
    rebuild=1
    shift
fi
if [[ $# -ne 2 ]]; then
    usage >&2
    exit 2
fi

output=$1
input=$2
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
repo_root=$(cd -- "$script_dir/.." && pwd -P)
cache_dir=${G1_NATIVE_SELFHOST_CACHE_DIR:-"$repo_root/target/native-selfhost"}
seed_dir=${G1_NATIVE_SELFHOST_SEED_DIR:-}
cache_marker="$cache_dir/.private-cache"
manifest="$cache_dir/manifest"
executable="$cache_dir/grandiose-self-host"
objects="$cache_dir/objects"

if [[ ! -f $input ]]; then
    printf 'native self-host: input does not exist: %s\n' "$input" >&2
    exit 2
fi

# A seed may come from a known-good primary worktree, but cache mutation is
# strictly local. This keeps independent /tmp worktrees from racing or silently
# consuming each other's partial outputs.
if [[ ! -e $cache_marker ]]; then
    mkdir -p "$cache_dir"
    if [[ -n $seed_dir ]]; then
        if [[ ! -d $seed_dir ]]; then
            printf 'native self-host: seed directory does not exist: %s\n' "$seed_dir" >&2
            exit 2
        fi
        cp -a -- "$seed_dir/." "$cache_dir/"
    fi
    : > "$cache_marker"
fi
mkdir -p "$objects"

if [[ -n ${G1_GRC_BIN:-} ]]; then
    grc=$G1_GRC_BIN
    if [[ ! -x $grc ]]; then
        printf 'native self-host: G1_GRC_BIN is not executable: %s\n' "$grc" >&2
        exit 2
    fi
else
    grc="$repo_root/target/release/grc"
    if [[ ! -x $grc ]]; then
        "$repo_root/tooling/ram-gate.sh" cargo build --release -p grandiose --bin grc
    fi
fi

if ! command -v wild >/dev/null 2>&1; then
    printf 'native self-host: Wild is required; install wild-linker and put `wild` on PATH.\n' >&2
    exit 2
fi

# The production compiler bundle excludes `self-host/src/probe`: those are
# independent test-only phase probes and their unclaimed modules must never be
# passed to the production module graph. The nested `foo/foo.glorious` layout
# is supplied as explicit segments because ordinary `mod foo` discovery looks
# for `foo.glorious`. `main.glorious` remains the primary segment.
self_host_main="$repo_root/self-host/src/main.glorious"
self_host_modules=(
    "$repo_root/self-host/src/frontend/frontend.glorious"
    "$repo_root/self-host/src/frontend/lexer/lexer.glorious"
    "$repo_root/self-host/src/frontend/lossless/lossless.glorious"
    "$repo_root/self-host/src/frontend/scanner/scanner.glorious"
    "$repo_root/self-host/src/frontend/headers/headers.glorious"
    "$repo_root/self-host/src/frontend/bodies/bodies.glorious"
    "$repo_root/self-host/src/frontend/resolution/resolution.glorious"
    "$repo_root/self-host/src/frontend/elaboration/elaboration.glorious"
    "$repo_root/self-host/src/backend/backend.glorious"
    "$repo_root/self-host/src/backend/artifact/artifact.glorious"
    "$repo_root/self-host/src/backend/lowering/lowering.glorious"
    "$repo_root/self-host/src/backend/emission/emission.glorious"
    "$repo_root/self-host/src/compiler/compiler.glorious"
    "$repo_root/self-host/src/diagnostics/diagnostics.glorious"
    "$repo_root/self-host/src/diagnostics/model/model.glorious"
    "$repo_root/self-host/src/diagnostics/source_errors/source_errors.glorious"
    "$repo_root/self-host/src/diagnostics/backend_errors/backend_errors.glorious"
)

# The native binary is valid only for the exact bootstrap binary and complete
# self-host source tree.
fingerprint=$(
    {
        printf 'schema=1\n'
        printf 'bootstrap-opt=O3\n'
        sha256sum "$grc"
        find "$repo_root/self-host/src" -path "$repo_root/self-host/src/probe" -prune -o -type f -name '*.glorious' -print0 | LC_ALL=C sort -z |
            xargs -0 sha256sum
    } | sha256sum | awk '{print $1}'
)

if [[ $rebuild -eq 1 || ! -x $executable || ! -f $manifest || $(<"$manifest") != "$fingerprint" ]]; then
    temporary="$executable.tmp.$$"
    rm -f -- "$temporary"
    printf 'native self-host: compiling release LLVM executable with Wild...\n' >&2
    set +e
    "$grc" -O3 --emit executable \
        -o "$temporary" "$self_host_main" "${self_host_modules[@]}"
    status=$?
    set -e
    if [[ $status -ne 0 ]]; then
        rm -f -- "$temporary"
        cat >&2 <<'EOF'
native self-host: LLVM could not compile the full self-host source above.
This runner intentionally has no VM-bytecode fallback. Unsupported LLVM lowering
diagnostics are authoritative; repair the reported source/backend capability before retrying.
EOF
        exit "$status"
    fi
    mv -f -- "$temporary" "$executable"
    printf '%s\n' "$fingerprint" > "$manifest"
fi

exec "$executable" "$output" "$input"
