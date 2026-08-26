#!/usr/bin/env bash
# Exercises a source-defined function body through scanner → Body → Core → MIR → VM.
set -euo pipefail

readonly root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
GRANDIOSE_STAGE0_SERVICE_PROBE="$root/self-host-stage0/probes/service_function_body.glorious" \
GRANDIOSE_STAGE0_SERVICE_EXPECTED=4408 \
"$root/tooling/self-host-stage0-service-check.sh"
