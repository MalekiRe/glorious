"""Mutation tests for the conformance plan gate, not language acceptance tests."""

from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
MODULE = importlib.util.spec_from_file_location("conformance_check", ROOT / "tooling/conformance_check.py")
assert MODULE is not None and MODULE.loader is not None
audit = importlib.util.module_from_spec(MODULE)
MODULE.loader.exec_module(audit)


class ConformancePlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.snapshot, cls.sections, cls.obligations = audit.scan_specs(ROOT)
        cls.cases = audit.read_tsv(ROOT / "conformance/cases.tsv", audit.CASE_COLUMNS)
        cls.matrix_data = json.loads((ROOT / "conformance/matrices.json").read_text())
        cls.matrices = audit.validate_matrices(cls.matrix_data)

    def validate(self, cases=None, sections=None):
        audit.validate_cases(self.cases if cases is None else cases,
                             self.sections if sections is None else sections,
                             self.obligations, self.matrices)

    def test_repository_plan_and_snapshot_are_consistent(self):
        audit.audit(ROOT)

    def test_checklists_are_current_48_language_and_96_library_families(self):
        self.assertEqual(self.obligations,
                         {f"L{i:02}" for i in range(1, 49)} | {f"S{i:02}" for i in range(1, 97)})

    def test_missing_checklist_case_is_rejected(self):
        with self.assertRaisesRegex(audit.AuditError, "checklist mismatch"):
            self.validate(self.cases[1:])

    def test_duplicate_case_is_rejected(self):
        with self.assertRaisesRegex(audit.AuditError, "duplicate"):
            self.validate(self.cases + [self.cases[0]])

    def test_unknown_checklist_case_is_rejected(self):
        cases = deepcopy(self.cases)
        cases[0]["id"] = "L99"
        with self.assertRaisesRegex(audit.AuditError, "checklist mismatch"):
            self.validate(cases)

    def test_new_prose_section_cannot_be_left_unrouted(self):
        sections = deepcopy(self.sections)
        sections["L99"] = {"units": [("prose", "A new semantic obligation.")]}
        with self.assertRaisesRegex(audit.AuditError, "unrouted"):
            self.validate(sections=sections)

    def test_unknown_section_is_rejected(self):
        cases = deepcopy(self.cases)
        cases[0]["sections"] = "L99"
        with self.assertRaisesRegex(audit.AuditError, "unknown spec section"):
            self.validate(cases)

    def test_unknown_expansion_is_rejected(self):
        cases = deepcopy(self.cases)
        cases[0]["matrices"] = "missing-matrix"
        with self.assertRaisesRegex(audit.AuditError, "unknown matrix"):
            self.validate(cases)

    def test_each_scenario_and_oracle_must_be_present(self):
        for field in ("positive", "negative", "boundary", "oracle"):
            with self.subTest(field=field):
                cases = deepcopy(self.cases)
                cases[0][field] = "TBD"
                with self.assertRaisesRegex(audit.AuditError, "underspecified"):
                    self.validate(cases)

    def test_duplicated_scenario_is_rejected(self):
        cases = deepcopy(self.cases)
        cases[0]["negative"] = cases[0]["positive"]
        with self.assertRaisesRegex(audit.AuditError, "scenarios are duplicated"):
            self.validate(cases)

    def test_plan_cannot_claim_passing_or_executable_evidence(self):
        for state in ("passed", "implemented", "ignored", "not-applicable"):
            cases = deepcopy(self.cases)
            cases[0]["state"] = state
            with self.subTest(state=state), self.assertRaisesRegex(audit.AuditError, "cannot claim"):
                self.validate(cases)

    def test_missing_conversion_pair_or_policy_is_rejected(self):
        for axis in ("source", "destination", "policy"):
            data = deepcopy(self.matrix_data)
            data["matrices"]["conversions"]["axes"][axis].pop()
            with self.subTest(axis=axis), self.assertRaisesRegex(audit.AuditError, "14 x 14 x 3"):
                audit.validate_matrices(data)

    def test_missing_integer_family_member_is_rejected(self):
        data = deepcopy(self.matrix_data)
        data["matrices"]["integers"]["axes"]["type"].remove("usize")
        with self.assertRaisesRegex(audit.AuditError, "twelve"):
            audit.validate_matrices(data)

    def test_review_units_include_prose_lists_tables_and_whole_code_blocks(self):
        lines = ["A declarative contract without MUST.", "", "* First rule.", "* Second rule.", "",
                 "| Name | Contract |", "|---|---|", "| item | rule |", "",
                 "```glorious", "pub fn a();", "pub fn b();", "```", "",
                 "**Rationale.** Explanation only."]
        units = audit.review_units(lines)
        self.assertEqual([kind for kind, _ in units], ["prose", "list", "list", "table", "table", "code"])
        self.assertIn("pub fn b();", units[-1][1])

    def test_fenced_heading_does_not_create_a_spec_section(self):
        text = "## 1. Scope\n```text\n## 9. not a heading\n```\n### 1.1 Rule\nBody.\n"
        self.assertEqual(set(audit.spec_sections(text, "L", 20)), {"L1", "L1.1"})

    def test_source_change_changes_snapshot_even_without_checklist_change(self):
        before = audit.review_units(["pub fields remain visible."])
        after = audit.review_units(["pub fields become private."])
        self.assertNotEqual(audit.digest(before[0][1]), audit.digest(after[0][1]))
        recorded = json.loads((ROOT / "conformance/spec-lock.json").read_text())
        mutated = deepcopy(recorded)
        next(iter(mutated["documents"].values()))["sha256"] = "0" * 64
        with patch.object(audit, "scan_specs", return_value=(mutated, self.sections, self.obligations)):
            with self.assertRaisesRegex(audit.AuditError, "specification drift"):
                audit.audit(ROOT)

    def test_tsv_extra_or_missing_columns_fail(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "invalid.tsv"
            for text in ("a\tb\nvalue\n", "a\tb\nvalue\tsecond\textra\n"):
                path.write_text(text)
                with self.subTest(text=text), self.assertRaisesRegex(audit.AuditError, "number of TSV"):
                    audit.read_tsv(path, ("a", "b"))

    def test_candidate_must_be_an_existing_enabled_test(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "candidate.rs"
            path.write_text("#[test]\nfn witness() {}\n")
            audit.validate_test_anchor(root, "candidate.rs::witness")
            for source in ("fn witness() {}\n", "#[test]\n#[ignore]\nfn witness() {}\n",
                           "#[test]\nfn renamed() {}\n"):
                path.write_text(source)
                with self.subTest(source=source), self.assertRaises(audit.AuditError):
                    audit.validate_test_anchor(root, "candidate.rs::witness")

    def test_candidate_cannot_be_promoted_by_changing_relation(self):
        candidates = [{"case_id": "L01", "test": "irrelevant.rs::test", "relation": "passed"}]
        with self.assertRaisesRegex(audit.AuditError, "not new conformance evidence"):
            audit.validate_candidates(ROOT, candidates, self.cases)

    def test_candidate_path_cannot_escape_repository(self):
        with self.assertRaisesRegex(audit.AuditError, "escapes repository"):
            audit.validate_test_anchor(ROOT, "../outside.rs::test")

    def test_readiness_is_red_even_when_plan_integrity_is_green(self):
        process = subprocess.run([sys.executable, str(ROOT / "tooling/conformance_check.py"),
                                  "--require-complete"], text=True, capture_output=True, timeout=30)
        self.assertEqual(process.returncode, 1, process.stdout + process.stderr)
        self.assertIn("Plan integrity OK", process.stdout)
        self.assertIn("Readiness FAILED", process.stderr)

    def test_cli_expansions_are_complete_and_do_not_claim_execution(self):
        def output(option):
            process = subprocess.run([sys.executable, str(ROOT / "tooling/conformance_check.py"), option],
                                     text=True, capture_output=True, timeout=30)
            self.assertEqual(process.returncode, 0, process.stderr)
            return json.loads(process.stdout)

        scenarios = output("--list-scenarios")
        self.assertEqual(len(scenarios), 3 * len(self.cases))
        self.assertEqual(len({row["id"] for row in scenarios}), len(scenarios))
        self.assertTrue(all(row["state"] == "planned" for row in scenarios))
        units = output("--list-units")
        self.assertTrue(all(row["cases"] and row["text"] for row in units))
        self.assertEqual(len(units), sum(len(section["units"]) for section in self.sections.values()))
        cells = output("--conversion-cells")
        self.assertEqual(len(cells), 588)
        self.assertEqual(len({(row["source"], row["destination"], row["policy"]) for row in cells}), 588)


if __name__ == "__main__":
    unittest.main()
