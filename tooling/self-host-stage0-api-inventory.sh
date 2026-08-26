#!/usr/bin/env bash
# Canonical inventory of the frozen Stage0 public module/re-export surface.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly stage0_root="${STAGE0_INVENTORY_STAGE0_ROOT:-$root/crates/grandiose-stage0}"
readonly library="$stage0_root/src/lib.rs"

printf 'kind\tdeclaration\n'
awk '
function flush() {
    sub(/^pub use /, "", text)
    sub(/;$/, "", text)
    gsub(/[[:space:]]+/, " ", text)
    print "reexport\t" text
    collecting = 0
    text = ""
}
/^pub mod [a-z_]+;$/ {
    item = $0
    sub(/^pub mod /, "", item)
    sub(/;$/, "", item)
    print "module\t" item
    next
}
/^pub use / {
    collecting = 1
    text = $0
    if (/;$/) flush()
    next
}
collecting {
    text = text " " $0
    if (/;$/) flush()
}
' "$library"
