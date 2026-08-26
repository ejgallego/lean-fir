#!/usr/bin/env python3
"""Focused negative tests for validation receipt reuse."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import validation_harness as harness
import verify_validation_reuse as reuse


class ValidationReuseTests(unittest.TestCase):
    def test_exact_receipt_does_not_rerun(self) -> None:
        runner = mock.Mock()
        matrix = {"selectedCases": ["a"]}
        with mock.patch.object(
            reuse, "verify_reusable_receipt", return_value=matrix
        ):
            observed, reran = reuse.ensure_reusable_receipt(
                Path("receipt.json"), Path("plan.json"), runner
            )
        self.assertIs(observed, matrix)
        self.assertFalse(reran)
        runner.assert_not_called()

    def test_stale_receipt_reruns_and_reverifies(self) -> None:
        runner = mock.Mock()
        matrix = {"selectedCases": ["a"]}
        with mock.patch.object(
            reuse,
            "verify_reusable_receipt",
            side_effect=[harness.ValidationError("stale"), matrix],
        ) as verifier:
            observed, reran = reuse.ensure_reusable_receipt(
                Path("receipt.json"), Path("plan.json"), runner
            )
        self.assertIs(observed, matrix)
        self.assertTrue(reran)
        runner.assert_called_once_with()
        self.assertEqual(verifier.call_count, 2)

    def test_still_stale_after_rerun_fails(self) -> None:
        runner = mock.Mock()
        with mock.patch.object(
            reuse,
            "verify_reusable_receipt",
            side_effect=[
                harness.ValidationError("stale"),
                harness.ValidationError("still stale"),
            ],
        ) as verifier:
            with self.assertRaisesRegex(
                harness.ValidationError, "still stale"
            ):
                reuse.ensure_reusable_receipt(
                    Path("receipt.json"), Path("plan.json"), runner
                )
        runner.assert_called_once_with()
        self.assertEqual(verifier.call_count, 2)

    def test_file_identity_fails_closed_on_content_and_symlink_drift(self) -> None:
        reuse.ROOT.joinpath(".deps").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=reuse.ROOT / ".deps") as directory:
            root = Path(directory)
            source = root / "tool"
            source.write_bytes(b"accepted")
            digest = harness.sha256_bytes(b"accepted")
            self.assertEqual(
                reuse.require_file_identity(digest, [source], "fixture"),
                source.resolve(),
            )
            source.write_bytes(b"stale")
            with self.assertRaisesRegex(
                harness.ValidationError, "no longer matches retained sha256"
            ):
                reuse.require_file_identity(digest, [source], "fixture")
            source.write_bytes(b"accepted")
            link = root / "tool-link"
            link.symlink_to(source)
            with self.assertRaisesRegex(
                harness.ValidationError, "no longer matches retained sha256"
            ):
                reuse.require_file_identity(digest, [link], "fixture")

    def test_current_control_input_drift_rejects_reuse(self) -> None:
        reuse.ROOT.joinpath(".deps").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=reuse.ROOT / ".deps") as directory:
            root = Path(directory)
            plan = root / "plan.json"
            plan.write_bytes(b"accepted\n")
            matrix = {
                "inputs": [
                    {
                        "kind": "corpus",
                        "name": "corpus.json",
                        "sha256": "0" * 64,
                    },
                    {
                        "kind": "validation-plan",
                        "name": "plan.json",
                        "sha256": harness.sha256_bytes(b"accepted\n"),
                    },
                ]
            }
            reuse.verify_current_inputs(matrix, root)
            plan.write_bytes(b"stale\n")
            with self.assertRaisesRegex(
                harness.ValidationError, "no longer matches retained sha256"
            ):
                reuse.verify_current_inputs(matrix, root)

    def test_requested_inventory_and_pairs_must_be_exactly_covered(self) -> None:
        reuse.ROOT.joinpath(".deps").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=reuse.ROOT / ".deps") as directory:
            root = Path(directory)
            plan = root / "plan.json"
            plan.write_text(
                json.dumps(
                    {
                        "version": 3,
                        "adapterConfigs": [],
                        "pairs": [
                            {"reference": "native", "candidate": "lcnf"}
                        ],
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            descriptors = [
                {"id": "a", "tags": []},
                {"id": "b", "tags": ["pending"]},
            ]
            matrix = {
                "selectedCases": ["a", "b"],
                "pairs": [
                    {"reference": "native", "candidate": "lcnf"},
                    {"reference": "native", "candidate": "v8"},
                ],
                "inputs": [],
            }
            reuse.verify_plan_coverage(matrix, descriptors, plan)
            matrix["selectedCases"] = ["a"]
            with self.assertRaisesRegex(
                harness.ValidationError, "selection does not exactly cover"
            ):
                reuse.verify_plan_coverage(matrix, descriptors, plan)
            matrix["selectedCases"] = ["a", "b"]
            matrix["pairs"] = [
                {"reference": "native", "candidate": "v8"}
            ]
            with self.assertRaisesRegex(
                harness.ValidationError, "missing requested comparison pair"
            ):
                reuse.verify_plan_coverage(matrix, descriptors, plan)


if __name__ == "__main__":
    unittest.main()
