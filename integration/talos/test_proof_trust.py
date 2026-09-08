"""Negative source-root regressions for the W6 trust gate."""

import importlib.util
from pathlib import Path
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("proof_trust", HERE / "check-proof-trust.py")
AUDIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(AUDIT)


class ProofTrustTests(unittest.TestCase):
    def setUp(self):
        scratch = AUDIT.ROOT / ".deps/proof-trust/tests"
        scratch.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=scratch)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for path, name in AUDIT.EXPECTED_AXIOMS:
            self.write(str(path), f"axiom {name} : True\n")

    def write(self, relative, content):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def test_integration_axiom_rejected(self):
        self.write("integration/talos/FirTalos/Bad.lean", "private axiom surprise : False\n")
        errors, _ = AUDIT.audit_sources(self.root)
        self.assertTrue(any("unexpected textual axiom surprise" in error for error in errors))

    def test_integration_placeholder_rejected(self):
        self.write("integration/talos/FirTalos/Bad.lean", "theorem bad : True := by sorry\n")
        errors, _ = AUDIT.audit_sources(self.root)
        self.assertTrue(any("proof placeholder" in error for error in errors))

    def test_umbrella_placeholder_rejected(self):
        self.write("integration/talos/FirTalos.lean", "example : True := by admit\n")
        errors, _ = AUDIT.audit_sources(self.root)
        self.assertTrue(any("proof placeholder" in error for error in errors))

    def test_comments_and_strings_ignored(self):
        self.write("integration/talos/FirTalos/Good.lean",
                   '/- sorry /- axiom nested : False -/ -/\n'
                   'def note := "sorry; axiom imaginary : False"\n'
                   '-- admit\ntheorem good : True := True.intro\n')
        self.assertEqual(AUDIT.audit_sources(self.root)[0], [])

    def test_missing_registered_bridge_rejected(self):
        for path, _ in AUDIT.EXPECTED_AXIOMS:
            (self.root / path).unlink()
        self.assertTrue(any("missing registered axiom" in error
                            for error in AUDIT.audit_sources(self.root)[0]))

    def test_dependency_sources_are_not_maintained_roots(self):
        self.write("integration/talos/.lake/packages/example/Bad.lean",
                   "axiom foreign : False\n")
        self.assertEqual(AUDIT.audit_sources(self.root)[0], [])


if __name__ == "__main__":
    unittest.main()
