"""Source coverage and authenticated command routing for the W6 trust gate."""

import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


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
        self.write(
            ".deps/talos-434/project/lean-toolchain",
            "leanprover/lean4:v4.34.1\n",
        )
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

    def test_retained_consumer_trust_regressions_rejected(self):
        for code, message in [
            ("private axiom surprise : False\n", "unexpected textual axiom surprise"),
            ("theorem bad : True := by sorry\n", "proof placeholder"),
        ]:
            with self.subTest(code=code):
                self.write("integration/talos/retained-initializer/Bad.lean", code)
                errors, _ = AUDIT.audit_sources(self.root)
                self.assertTrue(any(message in error for error in errors))

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

    def test_compiled_audit_prepares_current_project_and_forces_elaboration(self):
        project = self.root / ".deps/talos-434/project"
        # Legacy state must not determine where either Lean command executes.
        self.write("integration/talos/lean-toolchain", "leanprover/lean4:v4.34.1\n")
        with patch.dict(AUDIT.os.environ, {"ELAN_TOOLCHAIN": "obsolete"}), \
             patch.object(AUDIT.subprocess, "check_output", return_value="cache\n"), \
             patch.object(AUDIT.subprocess, "run",
                          return_value=subprocess.CompletedProcess([], 0)) as run:
            self.assertEqual(AUDIT.audit_compiled(self.root), 0)
        setup, identity, build, direct = run.call_args_list
        self.assertEqual(setup.args[0],
                         ["bash", str(self.root / "tooling/talos-434/setup.sh")])
        self.assertEqual(identity.args[0][2:],
                         ["--profile", "lean-4.34.1", "--lean-project", str(project)])
        self.assertEqual(build.args[0], ["lake", "build", "FirTalos.TrustAudit"])
        self.assertEqual(direct.args[0],
                         ["lake", "env", "lean", "FirTalos/TrustAudit.lean"])
        for prerequisite in (setup, identity, build):
            self.assertTrue(prerequisite.kwargs["check"])
        for command in (build, direct):
            self.assertEqual(command.kwargs["cwd"], project)
        for command in run.call_args_list:
            env = command.kwargs["env"]
            self.assertNotIn("ELAN_TOOLCHAIN", env)
            self.assertEqual(env["TMPDIR"], str(self.root / ".deps/proof-trust/tmp"))

    def test_compiled_audit_stops_on_setup_identity_or_build_failure(self):
        for failure_index in range(3):
            with self.subTest(failure_index=failure_index), \
                 patch.object(AUDIT.subprocess, "check_output", return_value="cache\n"), \
                 patch.object(AUDIT.subprocess, "run") as run:
                run.side_effect = [subprocess.CompletedProcess([], 0)] * failure_index + [
                    subprocess.CalledProcessError(1, "failed prerequisite")]
                with self.assertRaises(subprocess.CalledProcessError):
                    AUDIT.audit_compiled(self.root)
                self.assertEqual(run.call_count, failure_index + 1)

    def test_direct_audit_failure_propagates_after_successful_build(self):
        with patch.object(AUDIT.subprocess, "check_output", return_value="cache\n"), \
             patch.object(AUDIT.subprocess, "run") as run:
            run.side_effect = [subprocess.CompletedProcess([], 0)] * 3 + [
                subprocess.CompletedProcess([], 1)]
            self.assertEqual(AUDIT.audit_compiled(self.root), 1)


if __name__ == "__main__":
    unittest.main()
