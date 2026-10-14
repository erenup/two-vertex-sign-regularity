#!/usr/bin/env python3
"""Negative controls for source inspection, dependency output, and execution."""

from contextlib import redirect_stderr, redirect_stdout
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import verify


VALID_OUTPUT = (
    "'IV01.twoCheckerVertices' depends on axioms: "
    "[propext, Classical.choice, Quot.sound]\n"
)


class AuditControls(unittest.TestCase):
    def test_valid_sources_and_output(self):
        root = self.fixture()
        snapshot = verify.check_sources(root)
        self.assertIn("IV01/RankSelection.lean", snapshot)
        self.assertEqual(len(snapshot), 42)
        self.assertEqual(set(verify.check_configuration(root)), set(verify.CONFIGURATION_HASHES))
        self.assertEqual(verify.parse_axioms(VALID_OUTPUT), verify.EXPECTED_AXIOMS)
        self.assertEqual(verify.parse_axioms(VALID_OUTPUT.replace(
            "propext, Classical.choice, Quot.sound", "Quot.sound, propext, Classical.choice")),
            verify.EXPECTED_AXIOMS)

    def test_forbidden_proof_tokens(self):
        for source in (
            "theorem bad : False := by sorry",
            "theorem bad : False := by\n  admit",
            "axiom bad : False", "axiom/- declaration -/bad : False",
            "theorem bad : False := by\n  «sorry»",
            "theorem bad : False := by\n  exact sorryAx _ false",
            "unsafe def bad := 0", "by native_decide",
            "@[implemented_by bad] def safe := 0", "Lean.ofReduceBool",
            '/- sorry -/', 'def text := "admit"',
        ):
            with self.subTest(source=source), self.assertRaises(verify.AuditError):
                verify.reject_forbidden(source, "example.lean")

    def test_missing_extra_and_malformed_axiom_output(self):
        for output in (
            "", "Build completed successfully.\n", VALID_OUTPUT + VALID_OUTPUT,
            "unrelated output\n" + VALID_OUTPUT, VALID_OUTPUT + "extra output\n",
            VALID_OUTPUT.replace("twoCheckerVertices", "otherTheorem"),
            VALID_OUTPUT.replace("]", ", sorryAx]"),
            VALID_OUTPUT.replace(", Quot.sound", ""),
            VALID_OUTPUT.replace("Quot.sound", "propext"),
            VALID_OUTPUT.replace("]", ", propext]"),
            VALID_OUTPUT.replace("[propext, Classical.choice, Quot.sound]", "[]"),
            VALID_OUTPUT.replace("]", ""),
        ):
            with self.subTest(output=output), self.assertRaises(verify.AuditError):
                verify.parse_axioms(output)
        with self.assertRaises(verify.AuditError):
            verify.parse_axioms(VALID_OUTPUT, "warning: unexpected diagnostic\n")

    def fixture(self):
        temporary_root = verify.ROOT / ".lake"
        temporary_root.mkdir(exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix="audit-control-", dir=temporary_root)
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        names = (verify.check_source_bindings(verify.ROOT).keys()
                 | verify.REQUIRED_SOURCES | verify.CONFIGURATION_HASHES.keys()
                 | {verify.SOURCE_BINDINGS_PATH})
        for name in names:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((verify.ROOT / name).read_bytes())
        return root

    def test_manifest_bytes_and_pin(self):
        root = self.fixture()
        path = root / verify.SOURCE_BINDINGS_PATH
        original = path.read_bytes()
        path.write_bytes(original + b"\n")
        with self.assertRaisesRegex(verify.AuditError, "SHA256 pin"):
            verify.check_sources(root)
        path.write_bytes(original)
        with patch.object(verify, "SOURCE_BINDINGS_SHA256", "0" * 64):
            with self.assertRaisesRegex(verify.AuditError, "SHA256 pin"):
                verify.check_sources(root)

    def test_source_change_cannot_be_hidden_by_manifest_edit(self):
        root = self.fixture()
        source = root / "IV01" / "Induction.lean"
        source.write_bytes(source.read_bytes() + b"\n/- Additional comment. -/\n")
        with self.assertRaisesRegex(verify.AuditError, "Bound source changed"):
            verify.check_sources(root)
        path = root / verify.SOURCE_BINDINGS_PATH
        binding = json.loads(path.read_text(encoding="utf-8"))
        binding["source_hashes"]["IV01/Induction.lean"] = verify.hashlib.sha256(
            source.read_bytes()).hexdigest()
        path.write_text(json.dumps(binding, indent=2) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(verify.AuditError, "SHA256 pin"):
            verify.check_sources(root)

    def test_nonimported_source_inventory_is_fixed(self):
        root = self.fixture()
        path = root / "IV01" / "RankSelection.lean"
        data = path.read_bytes()
        path.unlink()
        with self.assertRaisesRegex(verify.AuditError, "Source inventory"):
            verify.check_sources(root)
        path.with_name("RenamedSelection.lean").write_bytes(data)
        with self.assertRaisesRegex(verify.AuditError, "Source inventory"):
            verify.check_sources(root)

    def test_source_binding_metadata_cannot_be_rewritten(self):
        for replacement in ({"schema": 2}, {"extra": "field"}, {"source_hashes": {}}):
            root = self.fixture()
            path = root / verify.SOURCE_BINDINGS_PATH
            binding = json.loads(path.read_text(encoding="utf-8"))
            binding.update(replacement)
            path.write_text(json.dumps(binding, indent=2) + "\n", encoding="utf-8")
            with self.subTest(replacement=replacement), self.assertRaisesRegex(
                    verify.AuditError, "SHA256 pin"):
                verify.check_sources(root)

    def test_missing_or_linked_source_binding(self):
        root = self.fixture()
        path = root / verify.SOURCE_BINDINGS_PATH
        path.unlink()
        with self.assertRaises(verify.AuditError):
            verify.check_sources(root)
        path.symlink_to(verify.ROOT / verify.SOURCE_BINDINGS_PATH)
        with self.assertRaises(verify.AuditError):
            verify.check_sources(root)

    def test_configuration_cannot_redirect_the_build(self):
        replacements = {
            "lakefile.toml": 'name = "iv01"\n[[lean_lib]]\nname = "IV01"\nsrcDir = "shadow"\n',
            "lean-toolchain": "leanprover/lean4:nightly\n",
            "lake-manifest.json": '{"packages": []}\n',
        }
        for name, replacement in replacements.items():
            root = self.fixture()
            (root / name).write_text(replacement, encoding="utf-8")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                verify.check_configuration(root)

    def test_missing_or_linked_configuration(self):
        for name in verify.CONFIGURATION_HASHES:
            root = self.fixture()
            path = root / name
            path.unlink()
            with self.subTest(name=name, linked=False), self.assertRaises(verify.AuditError):
                verify.check_configuration(root)
            path.symlink_to(verify.ROOT / name)
            with self.subTest(name=name, linked=True), self.assertRaises(verify.AuditError):
                verify.check_configuration(root)

    def test_nested_sources_and_dependency_exclusion(self):
        root = self.fixture()
        nested = root / "IV01" / "Nested" / "Bad.lean"
        nested.parent.mkdir()
        nested.write_text("theorem bad : False := by sorry\n", encoding="utf-8")
        with self.assertRaises(verify.AuditError):
            verify.check_sources(root)
        nested.write_text("theorem good : True := by trivial\n", encoding="utf-8")
        self.assertIn(nested, verify.source_paths(root))
        with self.assertRaisesRegex(verify.AuditError, "Source inventory"):
            verify.check_sources(root)
        nested.unlink()
        dependency = root / ".lake" / "packages" / "Dependency.lean"
        dependency.parent.mkdir(parents=True)
        dependency.write_text("axiom dependency : False\n", encoding="utf-8")
        self.assertNotIn(".lake/packages/Dependency.lean", verify.check_sources(root))

    def test_fixed_sources_cannot_be_spoofed_by_comments(self):
        for name in verify.FIXED_SOURCE_HASHES:
            root = self.fixture()
            path = root / name
            path.write_text("/-\n" + path.read_text(encoding="utf-8") + "\n-/\n",
                            encoding="utf-8")
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                verify.check_sources(root)

    def test_required_file_missing(self):
        for name in verify.REQUIRED_SOURCES:
            root = self.fixture()
            (root / name).unlink()
            with self.subTest(name=name), self.assertRaises(verify.AuditError):
                verify.check_sources(root)

    def test_forged_axiom_probe(self):
        root = self.fixture()
        (root / "audit" / "Axioms.lean").write_text(
            '#eval IO.println "' + VALID_OUTPUT.strip() + '"\n', encoding="utf-8")
        with self.assertRaises(verify.AuditError):
            verify.check_sources(root)

    def test_unexpected_lean_file(self):
        root = self.fixture()
        (root / "Unbuilt.lean").write_text("theorem unused : True := by trivial\n", encoding="utf-8")
        with self.assertRaises(verify.AuditError):
            verify.check_sources(root)

    def test_symlink_file_and_directory(self):
        for directory in (False, True):
            root = self.fixture()
            target = root / "IV01" if directory else root / "IV01.lean"
            link = root / ("Linked" if directory else "Linked.lean")
            link.symlink_to(target, target_is_directory=directory)
            with self.subTest(directory=directory), self.assertRaises(verify.AuditError):
                verify.check_sources(root)

    def test_execution_failure_cannot_be_hidden_by_valid_output(self):
        with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()):
            with self.assertRaises(verify.AuditError):
                verify.run_checked([sys.executable, "-c",
                                    f"print({VALID_OUTPUT!r}); raise SystemExit(7)"], verify.ROOT)
            with self.assertRaises(verify.AuditError):
                verify.run_checked(["./missing-audit-command"], verify.ROOT)
            result = verify.run_checked([sys.executable, "-c", f"print({VALID_OUTPUT!r})"], verify.ROOT)
        self.assertEqual(verify.parse_axioms(result.stdout), verify.EXPECTED_AXIOMS)


if __name__ == "__main__":
    unittest.main()
