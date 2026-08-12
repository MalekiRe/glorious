#!/usr/bin/env bash
# Keep the development self-host route on durable function objects.  It must
# never silently regress to a fresh monolithic native executable build.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
script="$repo_root/tooling/native-selfhost.sh"

grep -Fq 'objects="$cache_dir/objects"' "$script"
grep -Fq 'mkdir -p "$objects"' "$script"
grep -Fq -- '--native-incremental-cache "$objects"' "$script"
