#!/usr/bin/env bash
# Canonical source-level test inventory for the frozen Stage0 corpus.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly owners="$root/docs/self-host-stage0/test-owner-rules.tsv"
readonly stage0_root="${STAGE0_INVENTORY_STAGE0_ROOT:-$root/crates/grandiose-stage0}"
readonly prefix="${STAGE0_INVENTORY_PREFIX:-crates/grandiose-stage0}"
cd "$stage0_root"

[[ -f "$owners" ]] || { echo "self-host test inventory: missing owner rules" >&2; exit 1; }

# Source order is intentional: it makes a rename, deletion, or movement of a
# test a baseline-roll event rather than a silent corpus change.
awk -v prefix="$prefix" -F '\t' '
NR == FNR {
    if (FNR > 1) owner[$1] = $2
    next
}
FNR == 1 { pending = 0 }
/^[[:space:]]*#[[]test[]]/ { pending = 1; next }
pending && /^[[:space:]]*fn[[:space:]]+[A-Za-z0-9_]+/ {
    name = $0
    sub(/^[[:space:]]*fn[[:space:]]+/, "", name)
    sub(/\(.*/, "", name)
    canonical = prefix "/" FILENAME
    if (canonical in owner) {
        print canonical "::" name "\t" owner[canonical]
    } else if (FILENAME ~ /^src\/[a-z_]+\.rs$/) {
        module = FILENAME
        sub(/^.*\//, "", module)
        sub(/\.rs$/, "", module)
        print canonical "::" name "\tmodule:" module
    } else {
        print "self-host test inventory: no owner rule for " canonical > "/dev/stderr"
        exit 1
    }
    pending = 0
}
' "$owners" $(find src tests -type f -name '*.rs' | LC_ALL=C sort)
