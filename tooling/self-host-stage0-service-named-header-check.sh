#!/usr/bin/env bash
set -euo pipefail
readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/service_named_header.glorious" GRANDIOSE_STAGE0_SERVICE_EXPECTED=201 "$root/tooling/self-host-stage0-service-check.sh"
