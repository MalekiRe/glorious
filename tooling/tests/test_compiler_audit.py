"""Regression checks for the authoring source closure (no build required)."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    "compiler_audit", Path(__file__).resolve().parents[1] / "compiler-audit.py"
)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AuthoringClosureTests(unittest.TestCase):
    def test_tracks_nested_module_addition_modification_and_removal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            crate = root / "crates/grandiose-stage0"
            source = crate / "src"
            source.mkdir(parents=True)
            manifest = crate / "Cargo.toml"
            manifest.write_text('[package]\nname = "fixture"\n')
            (source / "lib.rs").write_text("mod lowering;\n")
            before = audit.authoring_closure(root)
            self.assertEqual(len(before), 2)
            self.assertIn("crates/grandiose-stage0/Cargo.toml", before)

            nested = source / "lowering" / "validate.rs"
            nested.parent.mkdir()
            nested.write_text("pub fn validate() {}\n")
            key = str(nested.relative_to(root))
            added = audit.authoring_closure(root)
            self.assertEqual(set(added) - set(before), {key})
            self.assertEqual(added[key], hashlib.sha256(nested.read_bytes()).hexdigest())

            nested.write_text("pub fn validate() { panic!() }\n")
            changed = audit.authoring_closure(root)
            self.assertNotEqual(changed[key], added[key])
            nested.unlink()
            self.assertEqual(audit.authoring_closure(root), before)

            manifest.write_text('[package]\nname = "changed"\n')
            self.assertNotEqual(audit.authoring_closure(root), before)


if __name__ == "__main__":
    unittest.main()
