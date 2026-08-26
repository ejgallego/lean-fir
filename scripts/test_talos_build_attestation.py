#!/usr/bin/env python3
"""Focused tests for the exact Talos build attestation."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

import talos_build_attestation as talos


class TalosBuildAttestationTests(unittest.TestCase):
    def test_canonical_receipt_round_trip_and_state_drift(self) -> None:
        talos.ROOT.joinpath(".deps").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=talos.ROOT / ".deps") as directory:
            receipt = Path(directory) / "receipt.json"
            accepted = {"schema": talos.SCHEMA, "identity": "a" * 64}
            changed = {"schema": talos.SCHEMA, "identity": "b" * 64}
            talos.write_attestation(receipt, accepted)
            with mock.patch.object(talos, "current_attestation", return_value=accepted):
                self.assertEqual(talos.verify_attestation(receipt), accepted)
            with mock.patch.object(talos, "current_attestation", return_value=changed):
                with self.assertRaisesRegex(talos.AttestationError, "does not match"):
                    talos.verify_attestation(receipt)

    def test_noncanonical_and_symlink_receipts_are_rejected(self) -> None:
        talos.ROOT.joinpath(".deps").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=talos.ROOT / ".deps") as directory:
            root = Path(directory)
            receipt = root / "receipt.json"
            receipt.write_text('{"identity": "x", "schema": "y"}\n', encoding="utf-8")
            with self.assertRaisesRegex(talos.AttestationError, "not canonical"):
                talos.read_attestation(receipt)
            target = root / "target.json"
            talos.write_attestation(target, {"schema": talos.SCHEMA})
            link = root / "link.json"
            link.symlink_to(target)
            with self.assertRaisesRegex(talos.AttestationError, "not a regular file"):
                talos.read_attestation(link)

    def test_file_records_reject_content_and_symlink_drift(self) -> None:
        talos.ROOT.joinpath(".deps").mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=talos.ROOT / ".deps") as directory:
            path = Path(directory) / "input.lean"
            path.write_bytes(b"accepted")
            first = talos.file_record(talos.ROOT, path)
            path.write_bytes(b"changed")
            self.assertNotEqual(talos.file_record(talos.ROOT, path), first)
            link = path.with_name("link.lean")
            link.symlink_to(path)
            with self.assertRaisesRegex(talos.AttestationError, "not a regular file"):
                talos.file_record(talos.ROOT, link)


if __name__ == "__main__":
    unittest.main()
