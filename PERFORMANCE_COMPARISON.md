# Stage replay performance comparison

## Workload

`self_hosted_stage_one_replay_emits_stage_two_in_release_vm` in release mode.

## Recorded baseline

The existing stage-replay log records this workload finishing in **1,790.98 s**.
That run then failed at an explicit source abort, so it is a timing of the same
workload only up to that failure.

## Current rerun

A current-main rerun was started after the integrated performance changes. Its
cold release build completed, and the test process later exited, but the
detached process did not preserve its final test output or elapsed time. There
is therefore **no valid current elapsed time** and no defensible speedup
percentage yet.

## Result

**Inconclusive.** Do not interpret this as either a speedup or slowdown. A
repeat with stdout/stderr and elapsed time captured to a persistent log is
required before reporting a percentage.
