#!/usr/bin/env python3
"""Negative controls for version-indexed trusted-assumption auditing."""

from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "validate_trusted_assumptions", ROOT / "scripts/validate_trusted_assumptions.py"
)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


class TrustedAssumptionProfileTests(unittest.TestCase):
    def test_only_exact_reviewed_identity_pairs_are_selected(self) -> None:
        self.assertEqual(
            AUDIT.select_profile(
                "leanprover/lean4:v4.33.0",
                "4.33.0",
                "d8b18978322de05a8f3dba51ef03cf5461676c17",
            ),
            "lean-4.33",
        )
        self.assertEqual(
            AUDIT.select_profile(
                "leanprover/lean4:v4.34.0-rc2",
                "4.34.0-rc2",
                "6a10ac8c22beadecabdbb0919c2b50214762f91d",
            ),
            "lean-4.34-rc2",
        )

    def test_unknown_and_crossed_identities_fail_closed(self) -> None:
        self.assertIsNone(AUDIT.select_profile(
            "leanprover/lean4:v4.35.0", "4.35.0", "0" * 40
        ))
        self.assertIsNone(AUDIT.select_profile(
            "leanprover/lean4:v4.34.0-rc2",
            "4.34.0-rc2",
            "d8b18978322de05a8f3dba51ef03cf5461676c17",
        ))
        self.assertIsNone(AUDIT.select_profile(
            "leanprover/lean4:v4.33.0",
            "4.33.0",
            "6a10ac8c22beadecabdbb0919c2b50214762f91d",
        ))

    def test_changed_or_missing_source_hash_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / ".deps") as directory:
            base = Path(directory)
            source = base / "Reviewed.lean"
            source.write_text("def reviewed := true\n", encoding="utf-8")
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            self.assertEqual(AUDIT.audit_hashes(
                base, {Path("Reviewed.lean"): digest}, "test"
            ), [])
            source.write_text("def reviewed := false\n", encoding="utf-8")
            self.assertEqual(len(AUDIT.audit_hashes(
                base, {Path("Reviewed.lean"): digest}, "test"
            )), 1)
            self.assertEqual(len(AUDIT.audit_hashes(
                base, {Path("Missing.lean"): digest}, "test"
            )), 1)

    def test_extra_and_missing_axioms_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT / ".deps") as directory:
            base = Path(directory)
            trusted = base / "Fir/LeanIR/Passes/AlphaEqvTrusted.lean"
            trusted.parent.mkdir(parents=True)
            trusted.write_text("axiom lean433UpstreamBridge : True\n", encoding="utf-8")
            self.assertEqual(AUDIT.audit_axioms(base), [])
            trusted.write_text("axiom otherBridge : True\n", encoding="utf-8")
            findings = AUDIT.audit_axioms(base)
            self.assertEqual(len(findings), 2)
            self.assertTrue(any("unexpected axiom otherBridge" in item for item in findings))
            self.assertTrue(any("missing registered axiom" in item for item in findings))


if __name__ == "__main__":
    unittest.main()
