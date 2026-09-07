#!/usr/bin/env python3
"""Audit conformance *groundwork*, never report planned semantics as passing.

Only the Python standard library is required. --print-lock emits a proposed
review snapshot to stdout; it does not update or approve anything on disk.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
SPECS = {
    "L": ("glorious-language-specification.md", 20),
    "S": ("glorious-standard-library-specification.md", 32),
}
CASE_COLUMNS = (
    "id", "sections", "harness", "positive", "negative", "boundary", "oracle",
    "matrices", "state",
)
CANDIDATE_COLUMNS = ("case_id", "test", "relation")
HARNESSES = {
    "admission", "compile", "compile-run", "differential", "fault-injection",
    "ffi", "golden", "instrumented", "lexer", "library", "metamorphic",
    "mixed", "model", "resource", "trace",
}
HEADING = re.compile(r"^#{2,3} (\d+(?:\.\d+)*)(?:\.)? (.+)$")
CASE_ID = re.compile(r"(?:[LS]\d{2}|[LS]X\d{2})\Z")


class AuditError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def read_tsv(path: Path, columns: tuple[str, ...]) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as source:
        reader = csv.DictReader(
            (line for line in source if line.strip() and not line.startswith("#")),
            delimiter="\t",
        )
        require(tuple(reader.fieldnames or ()) == columns, f"{path}: wrong TSV columns")
        rows = list(reader)
    for index, row in enumerate(rows, 2):
        require(None not in row and all(value is not None for value in row.values()),
                f"{path}:{index}: wrong number of TSV fields")
        require(all(value.strip() for value in row.values()),
                f"{path}:{index}: empty field")
    return rows


def spec_sections(text: str, prefix: str, last_section: int) -> dict[str, dict]:
    """Direct section content, not a parent duplicating all of its children."""
    result: dict[str, dict] = {}
    current = None
    fenced = False
    for number, line in enumerate(text.splitlines(), 1):
        if line.startswith("```"):
            fenced = not fenced
        heading = None if fenced else HEADING.match(line)
        if heading:
            section, title = heading.groups()
            current = None
            if int(section.split(".")[0]) <= last_section:
                current = prefix + section
                require(current not in result, f"duplicate section {current}")
                result[current] = {"title": title, "line": number, "lines": []}
        elif current is not None:
            result[current]["lines"].append(line)
    require(not fenced, f"{prefix}: unterminated specification code fence")
    return result


def review_units(lines: list[str]) -> list[tuple[str, str]]:
    """Lossless semantic-routing units, not a claim to parse atomic obligations.

    Each prose paragraph, list item, table row and entire fenced interface block
    remains visible. We deliberately do not grep only for uppercase MUST:
    signatures, ordinary declarative prose and control tables are normative too.
    Rationale paragraphs add no independent rule under language section 1.1.
    """
    units: list[tuple[str, str]] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        if not line.strip():
            index += 1
            continue
        if line.startswith("```"):
            start = index
            index += 1
            while index < len(lines) and not lines[index].startswith("```"):
                index += 1
            require(index < len(lines), "unterminated interface/code block")
            index += 1
            units.append(("code", "\n".join(lines[start:index])))
        elif line.startswith("|"):
            # Separators are formatting rather than a contract/table heading.
            if not re.fullmatch(r"[| :\-]+", line):
                units.append(("table", line))
            index += 1
        else:
            start = index
            index += 1
            is_list = bool(re.match(r"^(?:[*+-]|\d+\.) ", line))
            while index < len(lines) and lines[index].strip():
                if lines[index].startswith(("```", "|")):
                    break
                if re.match(r"^(?:[*+-]|\d+\.) ", lines[index]):
                    break
                index += 1
            body = "\n".join(lines[start:index])
            if not body.startswith("**Rationale.**"):
                units.append(("list" if is_list else "prose", body))
    return units


def scan_specs(root: Path) -> tuple[dict, dict, set[str]]:
    snapshot = {"schema": 1, "documents": {}}
    sections: dict[str, dict] = {}
    obligations: set[str] = set()
    for prefix, (filename, last) in SPECS.items():
        text = (root / filename).read_text(encoding="utf-8")
        document = {"sha256": digest(text), "sections": {}}
        for section, body in spec_sections(text, prefix, last).items():
            units = review_units(body["lines"])
            sections[section] = {**body, "units": units}
            if units:
                document["sections"][section] = {
                    "title": body["title"],
                    "line": body["line"],
                    "units": [
                        {"id": f"{section}:{index:02}", "kind": kind, "sha256": digest(content)}
                        for index, (kind, content) in enumerate(units, 1)
                    ],
                }
        snapshot["documents"][filename] = document
        ids = re.findall(rf"^\| ({prefix}\d{{2}}) \|", text, flags=re.MULTILINE)
        require(len(ids) == len(set(ids)), f"{filename}: duplicate checklist ID")
        require(ids, f"{filename}: missing conformance checklist")
        obligations.update(ids)
    return snapshot, sections, obligations


def comma_values(value: str, location: str) -> list[str]:
    result = value.split(",")
    require(all(item and item == item.strip() for item in result),
            f"{location}: empty or whitespace-padded reference")
    require(len(result) == len(set(result)), f"{location}: duplicate reference")
    return result


def validate_matrices(data: dict) -> dict:
    require(data.get("schema") == 1, "unknown matrix schema")
    matrices = data.get("matrices", {})
    require(bool(matrices), "empty expansion matrix inventory")
    for name, matrix in matrices.items():
        require(set(matrix) == {"axes", "rule"}, f"{name}: invalid matrix fields")
        require(isinstance(matrix["rule"], str) and len(matrix["rule"]) >= 30,
                f"{name}: missing expansion/selection rule")
        require(bool(matrix["axes"]), f"{name}: no axes")
        for axis, members in matrix["axes"].items():
            require(isinstance(members, list) and members
                    and all(isinstance(item, str) and item for item in members),
                    f"{name}/{axis}: invalid axis")
            require(len(set(members)) == len(members), f"{name}/{axis}: duplicate cell")
    integers = ["u8", "u16", "u32", "u64", "u128", "usize",
                "i8", "i16", "i32", "i64", "i128", "isize"]
    require(matrices.get("integers", {}).get("axes", {}).get("type") == integers,
            "integer expansion must cover all twelve concrete types")
    expected_scalars = integers + ["f32", "f64"]
    conversion = matrices.get("conversions", {}).get("axes", {})
    require(conversion == {"source": expected_scalars, "destination": expected_scalars,
                           "policy": ["As", "TryAs", "ExactAs"]},
            "conversion matrix must cover 14 x 14 x 3 policy/pair cells")
    return matrices


def validate_cases(rows: list[dict[str, str]], sections: dict,
                   obligations: set[str], matrices: dict) -> None:
    ids = [row["id"] for row in rows]
    require(len(ids) == len(set(ids)), "duplicate conformance case ID")
    require(all(CASE_ID.fullmatch(key) for key in ids), "invalid conformance case ID")
    checklist = {key for key in ids if re.fullmatch(r"[LS]\d{2}", key)}
    require(checklist == obligations,
            f"checklist mismatch: missing={sorted(obligations - checklist)}, "
            f"extra={sorted(checklist - obligations)}")
    covered: set[str] = set()
    used_matrices: set[str] = set()
    for row in rows:
        key = row["id"]
        require(row["harness"] in HARNESSES, f"{key}: unknown harness")
        # This initial artifact is a test plan. A future execution/evidence
        # schema must be added before anyone can promote a row to proven.
        require(row["state"] == "planned", f"{key}: plan cannot claim semantic execution")
        refs = comma_values(row["sections"], key)
        require(all(ref in sections for ref in refs), f"{key}: unknown spec section in {refs}")
        covered.update(refs)
        expansions = comma_values(row["matrices"], key)
        require(all(item in matrices for item in expansions), f"{key}: unknown matrix")
        used_matrices.update(expansions)
        for field in ("positive", "negative", "boundary", "oracle"):
            require(len(row[field]) >= 30, f"{key}: underspecified {field}")
            require(row[field].strip().lower() not in {"todo", "tbd", "not applicable"},
                    f"{key}: placeholder {field}")
        require(len({row[field] for field in ("positive", "negative", "boundary")}) == 3,
                f"{key}: scenarios are duplicated")
    required_sections = {key for key, value in sections.items() if value["units"]}
    require(required_sections <= covered,
            f"unrouted specification sections: {sorted(required_sections - covered)}")
    require(used_matrices == set(matrices),
            f"unused expansion matrices: {sorted(set(matrices) - used_matrices)}")


def validate_test_anchor(root: Path, anchor: str) -> None:
    path_name, separator, test = anchor.partition("::")
    require(bool(separator) and bool(re.fullmatch(r"[a-zA-Z_]\w*", test)),
            f"invalid candidate anchor {anchor}")
    path = root / path_name
    require(path.resolve().is_relative_to(root.resolve()), f"anchor escapes repository: {anchor}")
    require(path.suffix == ".rs" and path.is_file(), f"missing candidate file: {anchor}")
    text = path.read_text(encoding="utf-8")
    declaration = re.search(rf"(?m)^\s*(?:pub )?fn {re.escape(test)}\s*\(", text)
    require(declaration is not None, f"missing candidate test: {anchor}")
    attributes = []
    for line in reversed(text[:declaration.start()].splitlines()):
        stripped = line.strip()
        if not stripped and not attributes:
            continue
        if stripped.startswith("#["):
            attributes.append(stripped)
        else:
            break
    require("#[test]" in attributes, f"candidate is not a #[test]: {anchor}")
    require(not any(item.startswith("#[ignore") for item in attributes),
            f"candidate is ignored: {anchor}")


def validate_candidates(root: Path, rows: list[dict[str, str]], cases: list[dict[str, str]]) -> None:
    ids = {row["id"] for row in cases}
    seen = set()
    for row in rows:
        pair = (row["case_id"], row["test"])
        require(pair not in seen, f"duplicate candidate {pair}")
        seen.add(pair)
        require(row["case_id"] in ids, f"candidate references unknown case {pair[0]}")
        require(row["relation"] == "candidate-only", "old regression is not new conformance evidence")
        validate_test_anchor(root, row["test"])


def audit(root: Path, check_lock: bool = True) -> tuple[dict, dict, list, dict, list]:
    snapshot, sections, obligations = scan_specs(root)
    cases = read_tsv(root / "conformance/cases.tsv", CASE_COLUMNS)
    matrices = validate_matrices(json.loads((root / "conformance/matrices.json").read_text()))
    validate_cases(cases, sections, obligations, matrices)
    candidates = read_tsv(root / "conformance/regression-candidates.tsv", CANDIDATE_COLUMNS)
    validate_candidates(root, candidates, cases)
    if check_lock:
        recorded = json.loads((root / "conformance/spec-lock.json").read_text())
        require(recorded == snapshot,
                "specification drift: review changed prose/signatures/tables and case plans; "
                "--print-lock proposes a snapshot but does not approve coverage")
    return snapshot, sections, cases, matrices, candidates


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="check plan integrity (default), not semantics")
    mode.add_argument("--print-lock", action="store_true", help="print proposed reviewed-source snapshot")
    mode.add_argument("--list-scenarios", action="store_true", help="print stable planned scenario IDs as JSON")
    mode.add_argument("--list-units", action="store_true", help="print prose/table/code units and case routing")
    mode.add_argument("--conversion-cells", action="store_true", help="print all 588 required scalar policy/pairs")
    mode.add_argument("--require-complete", action="store_true", help="fail while semantic execution evidence is absent")
    args = parser.parse_args(argv)
    try:
        snapshot, sections, cases, matrices, candidates = audit(ROOT, not args.print_lock)
        if args.print_lock:
            print(json.dumps(snapshot, indent=2, ensure_ascii=False))
        elif args.list_scenarios:
            print(json.dumps([
                {"id": f"{row['id']}.{variant}", "state": row["state"],
                 "scenario": row[variant], "oracle": row["oracle"],
                 "sections": row["sections"].split(","), "matrices": row["matrices"].split(",")}
                for row in cases for variant in ("positive", "negative", "boundary")
            ], indent=2))
        elif args.list_units:
            print(json.dumps([
                {"id": f"{section}:{index:02}", "kind": kind, "text": content,
                 "cases": [row["id"] for row in cases if section in row["sections"].split(",")]}
                for section, value in sections.items()
                for index, (kind, content) in enumerate(value["units"], 1)
            ], indent=2, ensure_ascii=False))
        elif args.conversion_cells:
            axes = matrices["conversions"]["axes"]
            print(json.dumps([
                dict(zip(axes, cell)) for cell in itertools.product(*axes.values())
            ], indent=2))
        else:
            unit_count = sum(len(section["units"]) for section in sections.values())
            print(f"Plan integrity OK: {len(cases)} families, {len(cases) * 3} planned scenario slots, "
                  f"{unit_count} routed specification review units, {len(matrices)} expansion matrices, "
                  f"{len(candidates)} candidate regression links.")
            print("Semantic conformance: NOT ESTABLISHED. All case families remain planned; "
                  "candidate links are not passing evidence.")
            if args.require_complete:
                print("Readiness FAILED: executable per-scenario/profile evidence is still required.", file=sys.stderr)
                return 1
        return 0
    except (AuditError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"conformance audit failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
