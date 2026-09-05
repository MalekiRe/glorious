#!/usr/bin/env python3
"""Reproducible source closure and fail-closed GSC-2 readiness checks."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parent.parent
COMPILER = ROOT / "compiler"


def closure():
    files = sorted((COMPILER / "src").rglob("*.glorious"))
    files += sorted((ROOT / "stdlib").rglob("*.glorious"))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def frozen_tests(baseline):
    paths = subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", baseline, "crates/grandiose-stage0"], cwd=ROOT, text=True
    ).splitlines()
    rows = []
    for path in paths:
        if not path.endswith(".rs"):
            continue
        source = subprocess.check_output(["git", "show", f"{baseline}:{path}"], cwd=ROOT, text=True)
        for match in re.finditer(r"#\[test\]\s*(?:#\[[^\n]*\]\s*)*fn\s+(\w+)", source):
            rows.append((path, match.group(1), "open"))
    return sorted(rows)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--refresh", action="store_true")
    parser.add_argument("--release", action="store_true")
    args = parser.parse_args()
    pins = tomllib.loads((COMPILER / "spec/baselines.toml").read_text())
    for name in ("behavior", "authoring", "standard_library", "stage0_verifier", "g1_verifier"):
        subprocess.run(["git", "cat-file", "-e", pins[name] + "^{commit}"], cwd=ROOT, check=True)
    lock = COMPILER / "sources.lock"
    authoring_paths = ["crates/grandiose-stage0/src/core.rs", "crates/grandiose-stage0/src/service.rs",
                       "crates/grandiose-stage0/src/vm_backend.rs", "crates/grandiose-stage0/src/mir.rs",
                       "crates/grandiose-stage0/src/request.rs", "crates/grandiose-stage0/src/runtime_manifest.rs",
                       "crates/grandiose-stage0/src/bootstrap.rs", "crates/grandiose-stage0/src/placeflow.rs",
                       "crates/grandiose-stage0/src/signature.rs", "crates/grandiose-stage0/src/trait_solver.rs",
                       "crates/grandiose-stage0/src/coherence.rs", "crates/grandiose-stage0/src/resolution.rs"]
    expected = {"schema": 1, "algorithm": "sha256", "files": closure(),
                "authoring_overrides": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in authoring_paths}}
    # Shared raw storage is a native/runtime prerequisite, not compiler source
    # or a certificate that Glorious bytecode can use unsafe operations yet.
    runtime_paths = [ROOT / "Cargo.toml", ROOT / "Cargo.lock",
                     ROOT / "crates/grandiose-runtime/Cargo.toml",
                     ROOT / "crates/grandiose-vm/Cargo.toml",
                     ROOT / "crates/grandiose-vm/src/lib.rs"]
    runtime_paths += sorted((ROOT / "crates/grandiose-runtime/src").rglob("*.rs"))
    expected["runtime_support"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in runtime_paths}
    test_paths = sorted((COMPILER / "tests").rglob("*.glorious")) + [
        ROOT / "crates/grandiose-stage0/tests/gsc2.rs",
        ROOT / "crates/grandiose-stage0/tests/conversions.rs",
        ROOT / "crates/grandiose-stage0/tests/coherence.rs",
        ROOT / "crates/grandiose-stage0/tests/resolution.rs",
        ROOT / "crates/grandiose-stage0/tests/signature.rs",
        ROOT / "crates/grandiose-stage0/tests/trait_solver.rs",
        ROOT / "crates/grandiose-stage0/tests/core.rs",
        ROOT / "crates/grandiose-stage0/tests/service.rs",
        ROOT / "crates/grandiose-stage0/tests/standard_library.rs",
        ROOT / "crates/grandiose-stage0/tests/vm_backend.rs",
        ROOT / "crates/grandiose-stage0/tests/request_and_revision.rs",
        ROOT / "crates/grandiose-stage0/tests/runtime_manifest.rs",
        ROOT / "crates/grandiose-stage0/tests/runtime_storage.rs",
        ROOT / "crates/grandiose-stage0/tests/fixtures/hash_indexing_profile.glorious",
        ROOT / "crates/grandiose-stage0/tests/fixtures/array_update_profile.glorious",
        ROOT / "crates/grandiose-vm/tests/native_memory.rs",
    ]
    expected["capability_tests"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in test_paths}
    expected["inventories"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted((COMPILER / "spec").glob("*.tsv"))}
    if args.refresh:
        with (COMPILER / "spec/oracle-tests.tsv").open("w") as output:
            writer = csv.writer(output, delimiter="\t", lineterminator="\n")
            writer.writerow(("file", "test", "status"))
            writer.writerows(frozen_tests(pins["behavior"]))
        spec = (ROOT / pins["specification"]).read_text()
        with (COMPILER / "spec/acceptance.tsv").open("w") as output:
            writer = csv.writer(output, delimiter="\t", lineterminator="\n")
            writer.writerow(("id", "contract", "status"))
            writer.writerows((m[1], m[2].strip(), "open") for m in
                             re.finditer(r"^\| ([QRICDBM][0-9]{2}) \| (.*?) \|$", spec, re.M))
        expected["inventories"] = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in sorted((COMPILER / "spec").glob("*.tsv"))}
        lock.write_text(json.dumps(expected, indent=2, sort_keys=True) + "\n")
    if json.loads(lock.read_text()) != expected:
        raise SystemExit("source closure changed: run tooling/compiler-audit.py --refresh")
    if (ROOT / "self-host-stage0").exists() or list((ROOT / "tooling").glob("self-host-*.sh")):
        raise SystemExit("retired implementation is active")
    for path in (COMPILER / "src").rglob("*"):
        if not path.is_file():
            continue
        if path.suffix != ".glorious":
            raise SystemExit(f"non-source compiler implementation: {path}")
        if re.search(r"self[-_]host[-_]stage0|compiler_support|host\s+.*\b(compile|query|resolve|type_check|emit_artifact)\b", path.read_text()):
            raise SystemExit(f"forbidden compiler dependency: {path}")
    with (COMPILER / "spec/contracts.tsv").open() as source:
        contracts = list(csv.DictReader(source, delimiter="\t"))
    if not contracts or any(not row["owner"] or not row["comparator"] or not row["oracle_command"] for row in contracts):
        raise SystemExit("contract owner/comparator missing")
    for command in {row["oracle_command"] for row in contracts}:
        if " --test " in command:
            target = command.split(" --test ", 1)[1]
            subprocess.run(["git", "cat-file", "-e", f"{pins['behavior']}:crates/grandiose-stage0/tests/{target}.rs"],
                           cwd=ROOT, check=True)
    exports = {row["export"] for row in contracts}
    required = {"grandiose_stage0::query::QueryEngine::execute", "grandiose_stage0::revision::CompilerDatabase::collect_retired",
                "grandiose_stage0::vm_backend::decode_and_verify_program", "grandiose_stage0::quantity::Quantity::upper"}
    if not required <= exports:
        raise SystemExit("inventory omits recursively reachable API")
    open_count = sum(row["status"] != "passed" for row in contracts)
    print(f"GSC-2: {len(expected['files'])} locked source files; {len(contracts)} public contracts; {open_count} open")
    if args.release:
        # Passing development tests never implicitly creates release evidence.
        raise SystemExit("release blocked: full contract comparisons and verified C2/C3 bootstrap evidence are required")


if __name__ == "__main__":
    main()
