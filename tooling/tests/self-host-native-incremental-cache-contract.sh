#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
script="$repo_root/tooling/self-host-native.sh"

bash -n "$script"
grep -Fq 'readonly route_cache="$route_root/target/self-host-native-cache"' "$script"
grep -Fq 'readonly route_objects="$route_cache/objects"' "$script"
grep -Fq -- '--native-incremental-cache "$route_objects"' "$script"
