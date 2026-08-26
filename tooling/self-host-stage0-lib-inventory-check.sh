#!/usr/bin/env bash
# Keep the source-level public facade synchronized with the generated Rust
# module inventory. This is an inventory check only; it does not claim API
# parity for the still-scaffolded facades.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
readonly inventory="$root/tooling/self-host-stage0-api-inventory.sh"
readonly facade="$root/self-host-stage0/src/lib/lib.glorious"

[[ -x "$inventory" && -f "$facade" ]] || {
    echo "self-host lib inventory: missing inventory generator or source facade" >&2
    exit 1
}

to_variant() {
    awk -F '_' '{
        value = ""
        for (part = 1; part <= NF; part++) {
            value = value toupper(substr($part, 1, 1)) substr($part, 2)
        }
        print value
    }'
}

mapfile -t expected < <(
    "$inventory" | awk -F '\t' '$1 == "module" { print $2 }' | to_variant | LC_ALL=C sort
)
mapfile -t actual < <(
    sed -n '/^pub enum PublicModule {/,/^}/p' "$facade" \
        | sed '1d;$d' \
        | rg -o '[A-Z][A-Za-z0-9]*' \
        | LC_ALL=C sort -u
)

[[ "${#expected[@]}" -gt 0 ]] || {
    echo "self-host lib inventory: generated Rust module inventory is empty" >&2
    exit 1
}
diff -u <(printf '%s\n' "${expected[@]}") <(printf '%s\n' "${actual[@]}") || {
    echo "self-host lib inventory: PublicModule does not match the generated Rust module inventory" >&2
    exit 1
}
printf '%s\n' "${#actual[@]}"
