# Subsecond compiler probe (experimental)

This isolated workspace has no effect on compiler dependencies or normal Cargo
profiles. Each tick builds a new compiler request and verifies/executes its
artifact, checking the result is 42. No compiler state survives a tick.

The installed `dx` is 0.7.6. The runtime and protocol lockfile are matched to it.
From this directory, run:

```sh
CARGO_BUILD_JOBS=2 ../test-with-budget.sh ../ram-gate.sh \
  dx serve --platform desktop --hot-patch --hot-reload true \
  --open false --interactive false --addr 127.0.0.1 --port 18083 --skip-assets
```

There is no GUI. Change the marker in `src/main.rs`; success requires the new
marker **and the same PID with a continuing tick counter**. A patch-build
message alone is not evidence that the process executed new code.

September 8 experiment: initial builds took about 29 seconds; tip-crate patches
took 121–130 ms. The patch-applied callback fired, but the original capturing
closure kept running old code. Subsecond 0.7.6's pointer-sized closure path
bypasses detouring. The current function-item boundary avoids that path, but
that follow-up has **not been restarted or validated**: work returned to
compiler implementation at the user's request. Compiler-library patching is
also unverified. No probe server was left running.

Do not use this as correctness or benchmark evidence. Restart after changes to
types/layouts, globals, callback signatures, or dependencies. See the upstream
[Subsecond limitations](https://docs.rs/subsecond/latest/subsecond/).
