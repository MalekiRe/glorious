#!/bin/sh
# Everything that is checked before a change is kept: the build, every test
# program and example on the Core machine, the Lean bytecode machine and the
# Rust VM, what `Glorious/Checks.lean` asks, and every program again on the
# interpreter, x86-64, LLVM and mixtures of them. Run from the repository's
# root; the VM is built first if it is not (`cargo build --release` in `vm`).
# `QUICK=0 ./verify.sh` builds the compiler as a release is built: slower to
# build, and nearly twice as fast to run.
set -eu
if [ "${QUICK-1}" = 0 ]; then lake build -R glorious; else lake build -R -Kquick=1 glorious; fi
[ -x vm/target/release/glorious-vm ] || (cd vm && cargo build --release)
.lake/build/bin/glorious selftest vm/target/release/glorious-vm
./vm/check-backends.sh | tail -4
