#!/usr/bin/env bash
set -euo pipefail

root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

count_tree() {
    local path="$1"
    find "$path" -name '*.glorious' -print0 \
        | xargs -0 awk '
            BEGIN { physical = 0; normalized = 0 }
            {
                physical += 1
                line = $0
                sub(/^[[:space:]]+/, "", line)
                if (line != "" && substr(line, 1, 2) != "//") {
                    normalized += 1
                }
            }
            END { printf "%d %d\n", physical, normalized }
        '
}

report() {
    local label="$1"
    local path="$2"
    local counts
    counts="$(count_tree "$path")"
    printf '%-12s %10s %10s\n' "$label" ${counts}
}

printf '%-12s %10s %10s\n' component physical normalized
report frontend "$root/src/frontend"
report backend "$root/src/backend"
report compiler "$root/src/compiler"
report diagnostics "$root/src/diagnostics"
report probes "$root/src/probe"

production_counts="$({
    find "$root/src" -path "$root/src/probe" -prune -o \
        -name '*.glorious' -print0
} | xargs -0 awk '
    BEGIN { physical = 0; normalized = 0 }
    {
        physical += 1
        line = $0
        sub(/^[[:space:]]+/, "", line)
        if (line != "" && substr(line, 1, 2) != "//") {
            normalized += 1
        }
    }
    END { printf "%d %d\n", physical, normalized }
')"
printf '%-12s %10s %10s\n' production ${production_counts}
report total "$root/src"
