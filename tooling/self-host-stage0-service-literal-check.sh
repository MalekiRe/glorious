#!/usr/bin/env bash
# Exercises immutable source decimal decoding through Body→Core→MIR→VM.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/service_literal.glorious" \
GRANDIOSE_STAGE0_SERVICE_EXPECTED=3291 \
"$root/tooling/self-host-stage0-service-check.sh"
