#!/usr/bin/env python3
"""Rejection controls for isolated compiler inputs and fresh output paths."""

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("standalone_verify", ROOT / "verify.py")
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)


class StandaloneControls(unittest.TestCase):
    def temporary(self):
        base = ROOT / ".lake"
        base.mkdir(exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix="standalone-controls-", dir=base)
        self.addCleanup(temporary.cleanup)
        return Path(temporary.name)

    def test_module_order_complete(self):
        sources = verify.audit.check_sources(ROOT)
        order = verify.module_order(sources)
        self.assertEqual(len(order), 41)
        self.assertEqual(len(set(order)), 41)
        self.assertLess(order.index("IV01.Statement"), order.index("IV01"))

    def test_cycle_and_missing_local_import(self):
        for sources in [
            {"IV01.lean": b"import IV01.A\n", "IV01/A.lean": b"import IV01\n"},
            {"IV01.lean": b"import IV01.Missing\n"},
        ]:
            with self.subTest(sources=sources), self.assertRaises(verify.audit.AuditError):
                verify.module_order(sources)

    def test_changed_compiler_rejected(self):
        compiler = self.temporary() / "lean"
        compiler.write_bytes(b"invalid compiler")
        with self.assertRaisesRegex(verify.audit.AuditError, "Compiler digest"):
            verify.dependencies(compiler)

    def test_existing_and_linked_output_rejected(self):
        root = self.temporary()
        compiler = root / "compiler/bin/lean"
        compiler.parent.mkdir(parents=True)
        existing = root / "existing"
        existing.mkdir()
        linked = root / "linked"
        linked.symlink_to(existing, target_is_directory=True)
        for path in [existing, linked, linked / "new"]:
            with self.subTest(path=path), self.assertRaises(verify.audit.AuditError):
                verify.prepare_output(path, compiler)

    def test_output_cannot_overlap_lake(self):
        root = self.temporary()
        compiler = root / "compiler/bin/lean"
        compiler.parent.mkdir(parents=True)
        with self.assertRaisesRegex(verify.audit.AuditError, "overlaps Lake"):
            verify.prepare_output(root / "objects", compiler)

    def test_library_links_rejected(self):
        root = self.temporary()
        library = root / "library"
        library.mkdir()
        target = library / "ordinary.olean"
        target.write_bytes(b"object")
        (library / "linked.olean").symlink_to(target)
        with self.assertRaisesRegex(verify.audit.AuditError, "linked library"):
            verify.artifacts(library)
        self.assertEqual(len(verify.artifacts(library, allow_internal_links=True)), 2)
        (library / "outside.olean").symlink_to(ROOT / "IV01.lean")
        with self.assertRaisesRegex(verify.audit.AuditError, "linked library"):
            verify.artifacts(library, allow_internal_links=True)

    def test_shadowed_theorem_object_rejected(self):
        root = self.temporary()
        for name in ["IV01.olean", "IV01/Statement.olean"]:
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"object")
            with self.subTest(name=name), self.assertRaisesRegex(
                    verify.audit.AuditError, "shadows a dependency"):
                verify.artifacts(root)
            path.unlink()

    def test_failed_command_rejected(self):
        with self.assertRaisesRegex(verify.audit.AuditError, "Command failed"):
            verify.run([sys.executable, "-c", "print('PASS'); raise SystemExit(7)"])
        with self.assertRaisesRegex(verify.audit.AuditError, "could not finish"):
            verify.run([str(self.temporary() / "missing")])


if __name__ == "__main__":
    unittest.main()
