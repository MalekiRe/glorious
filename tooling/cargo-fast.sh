#!/usr/bin/env bash
# Opt-in edit/check/test profile; ordinary Cargo and CI remain unchanged.
set -euo pipefail

if [[ ${1:-} == --help || $# == 0 ]]; then
    echo 'usage: bash tooling/cargo-fast.sh {build|check|test} [cargo arguments...]'
    echo 'G1_RUST_BACKEND=cranelift|llvm (default llvm)'
    echo 'G1_RUST_LINKER=mold|wild (default mold); G1_RUST_OPT_LEVEL=0|1|2|3 (default 1)'
    echo 'G1_RUST_TOOLCHAIN=nightly by default; CARGO_TARGET_DIR may override the isolated cache.'
    exit 0
fi
case "$1" in build|check|test) ;; *) echo 'cargo-fast: expected build, check, or test' >&2; exit 2 ;; esac
backend=${G1_RUST_BACKEND:-llvm}
linker=${G1_RUST_LINKER:-mold}
opt=${G1_RUST_OPT_LEVEL:-1}
case "$backend" in cranelift|llvm) ;; *) echo 'cargo-fast: unknown backend' >&2; exit 2 ;; esac
case "$linker" in mold|wild) ;; *) echo 'cargo-fast: unknown linker' >&2; exit 2 ;; esac
case "$opt" in 0|1|2|3) ;; *) echo 'cargo-fast: invalid optimization level' >&2; exit 2 ;; esac
for tool in cargo rustup clang "$linker"; do
    command -v "$tool" >/dev/null || { echo "cargo-fast: missing $tool" >&2; exit 2; }
done
if [[ -n ${RUSTFLAGS:-} || -n ${CARGO_ENCODED_RUSTFLAGS:-} ]]; then
    echo 'cargo-fast: unset RUSTFLAGS/CARGO_ENCODED_RUSTFLAGS; this wrapper owns its codegen flags' >&2
    exit 2
fi
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"
export RUSTUP_TOOLCHAIN=${G1_RUST_TOOLCHAIN:-nightly}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-"$repo_root/target/rust-fast-$backend-$linker-opt$opt"}
export CARGO_INCREMENTAL=1
export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
export CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0
export CARGO_PROFILE_DEV_OPT_LEVEL=$opt CARGO_PROFILE_TEST_OPT_LEVEL=$opt
# Keep assertions, overflow checks, and unwinding; never use panic=abort here.
export CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=true CARGO_PROFILE_TEST_DEBUG_ASSERTIONS=true
export CARGO_PROFILE_DEV_OVERFLOW_CHECKS=true CARGO_PROFILE_TEST_OVERFLOW_CHECKS=true
export RUSTFLAGS='-C linker=clang'
if [[ $backend == cranelift ]]; then
    echo 'cargo-fast: experimental Cranelift; installed backend fails the panic-recovery regression' >&2
    export RUSTFLAGS="-Zcodegen-backend=cranelift $RUSTFLAGS"
fi
if [[ $linker == mold ]]; then
    export RUSTFLAGS="$RUSTFLAGS -C link-arg=-fuse-ld=mold"
else
    export RUSTFLAGS="$RUSTFLAGS -C link-arg=--ld-path=wild"
fi
exec "$repo_root/tooling/test-with-budget.sh" "$repo_root/tooling/ram-gate.sh" cargo "$@"
