#!/usr/bin/env python3
"""Execute source capabilities and publish evidence only after the test run."""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--filter", action="append", default=[],
                        help="Run selected libtest name matches; evidence is explicitly partial.")
    args = parser.parse_args()
    subprocess.run(["python3", "tooling/compiler-audit.py"], cwd=ROOT, check=True)
    source_lock = (ROOT / "compiler/sources.lock").read_bytes()
    output = ROOT / "target" / "compiler-check"
    output.mkdir(parents=True, exist_ok=True)
    evidence = Path(tempfile.mkdtemp(prefix="run-", dir=output))
    environment = os.environ.copy()
    environment["GSC2_EVIDENCE_DIR"] = str(evidence)
    # These independent C0 compilations otherwise exceed the command budget
    # when ram-gate's general-purpose single-thread default is used. Keep the
    # memory/time guards in place and allow callers to choose fewer workers.
    environment.setdefault("RUST_TEST_THREADS", "8")
    # Optimize the native authoring compiler, not the emitted source program.
    # Keep test/debug assertions and the same time, VM, and memory guards. The
    # expanded source closure otherwise outgrows the unoptimized test budget.
    environment.setdefault("CARGO_PROFILE_TEST_OPT_LEVEL", "1")
    command = ["tooling/test-with-budget.sh", "tooling/ram-gate.sh", "cargo", "test",
               "-p", "grandiose-stage0", "--test", "gsc2"]
    if args.filter:
        command += ["--", *args.filter]
    result = subprocess.run(command, cwd=ROOT, env=environment, check=False)
    audit = subprocess.run(["python3", "tooling/compiler-audit.py"], cwd=ROOT, check=False)
    unchanged = (ROOT / "compiler/sources.lock").read_bytes() == source_lock
    exit_code = result.returncode or audit.returncode or (0 if unchanged else 1)
    records = []
    for path in sorted(evidence.glob("*.tsv")):
        with path.open() as source:
            records.extend(csv.DictReader(source, delimiter="\t"))
    # A successful zero-test match is not executed capability evidence.
    if not records and not exit_code:
        exit_code = 1
    report = {
        "schema": 1,
        "source_lock_sha256": hashlib.sha256(source_lock).hexdigest(),
        "command": command,
        "test_filters": args.filter,
        "test_scope": "selected_tests" if args.filter else "complete_current_suite",
        "test_threads": environment["RUST_TEST_THREADS"],
        "authoring_test_opt_level": environment["CARGO_PROFILE_TEST_OPT_LEVEL"],
        "exit_code": exit_code,
        "capability_run_passed": exit_code == 0 and bool(records),
        "complete_current_suite_passed": not args.filter and exit_code == 0 and bool(records),
        "release_ready": False,
        "execution_mode": "locally_compiled_source_with_trusted_unsafe_standard_library",
        "in_process_memory_sandbox": False,
        "scope": "source kernel, source admission/products, and typed source-query registry histories; no language parity or self-host bootstrap certification",
        "allocation_scope": "charged VM budget elements, not a census of physical allocations",
        "unprofiled_counters": "empty, not zero; see each execution's profiled field",
        "executions": records,
    }
    report_path = evidence / "report.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(f"GSC-2 execution evidence: {report_path}", flush=True)
    raise SystemExit(exit_code if exit_code else (0 if records else 1))


if __name__ == "__main__":
    main()
