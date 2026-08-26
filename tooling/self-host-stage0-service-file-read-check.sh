#!/usr/bin/env bash
# Proves file capability reaches the compiler service only through SourceInput.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/service_file_header.glorious" \
GRANDIOSE_STAGE0_SERVICE_EXPECTED=1423 \
"$root/tooling/self-host-stage0-service-check.sh" \
    --runtime-host file_read __g1_fs_read crate read_file \
    --capability file_read
