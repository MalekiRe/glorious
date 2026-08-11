#!/usr/bin/env bash
# Native self-host tests must use the production partitioned object-cache
# route. Direct Rust test-side LLVM emission plus clang defeats incremental
# iteration and is intentionally forbidden here.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)
test_root="$repo_root/crates/grandiose/tests"

if rg -n 'Command::new\("clang"\)|emit_llvm_ir\(|LlvmOptions' \
    "$test_root"/self_host_*.rs; then
    echo "self-host native tests must use the cached release CLI launcher" >&2
    exit 1
fi

support="$test_root/support/native_incremental.rs"
rg -Fq -- '--native-incremental-cache' "$support"
rg -Fq -- '"-O3", "--emit", "executable"' "$support"
