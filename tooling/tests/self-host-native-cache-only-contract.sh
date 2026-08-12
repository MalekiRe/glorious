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

# The full copied-self-host warm-edit integration harness lives with the CLI
# protocol tests rather than under self_host_*.  Keep its process-local serve
# state and private durable cache explicit as well: otherwise it could regress
# to a fresh native executable compile without this contract's glob seeing it.
release_harness="$test_root/grc_cli.rs"
rg -Fq -- 'fn release_selfhost_serve_warm_body_edit_reuses_cached_work()' "$release_harness"
rg -Fq -- '"--native-incremental".to_owned()' "$release_harness"
rg -Fq -- '"--native-incremental-cache".to_owned()' "$release_harness"
rg -Fq -- 'edited["cache_stats"]["bodies_reused"]' "$release_harness"
rg -Fq -- 'durable_object_manifests(&cache)' "$release_harness"

# The opt-in native CLI self-host gate may run under Rust's parallel test
# harness. Its durable cache must live below the per-invocation trace root,
# never in a worktree-wide directory shared by concurrent test processes.
native_cli_gate="$repo_root/crates/grandiose/tests/self_host_bytecode.rs"
rg -Fq -- 'let cache = trace.join("native-incremental-cache");' "$native_cli_gate"
if rg -Fq -- 'G1_SELF_HOST_NATIVE_CLI_CACHE_DIR' "$native_cli_gate"; then
    echo "native CLI self-host gate permits a shared durable cache override" >&2
    exit 1
fi
