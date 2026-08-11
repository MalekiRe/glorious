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
rg -Fq -- 'target/release/grc' "$support"
rg -Fq -- 'directory.join("native-incremental-cache")' "$support"

# A native self-host test may use the shared launcher or (for the retained
# stage-convergence trace) invoke release `grc` itself.  Either way, every
# executable-emission test file must visibly select the durable cache.  This
# closes the gap where a future test could avoid direct clang yet still cause a
# fresh monolithic O3 executable compile on every run.
while IFS=: read -r test_file _; do
    rg -Fq -- '--native-incremental-cache' "$test_file" || {
        echo "native self-host executable emission lacks --native-incremental-cache: $test_file" >&2
        exit 1
    }
done < <(
    rg -l --glob 'self_host_*.rs' \
        '"--emit", "executable"|"--emit executable"|--emit executable' \
        "$test_root"
)
