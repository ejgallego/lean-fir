#!/usr/bin/env python3
"""Deletion boundaries for disposable validation scratch."""

from pathlib import Path
import tempfile
import unittest
from unittest import mock

import clean_validation as scratch


class CleanValidationTests(unittest.TestCase):
    def setUp(self):
        scratch.ROOT.joinpath(".deps").mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=scratch.ROOT / ".deps")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def test_only_named_scratch_is_removed_and_repeated_cleanup_is_safe(self):
        for name in (*scratch.DIRECTORIES, "talos-check", "release-package"):
            target = self.root / "_build" / name
            target.mkdir(parents=True)
            (target / "data").write_text("retained or disposable")
        with mock.patch.object(scratch.subprocess, "check_output", return_value=b""):
            scratch.clean(self.root)
            scratch.clean(self.root)
        for name in scratch.DIRECTORIES:
            self.assertFalse((self.root / "_build" / name).exists())
        for name in ("talos-check", "release-package"):
            self.assertTrue((self.root / "_build" / name / "data").exists())

    def test_symlinked_build_is_rejected(self):
        outside = self.root / "outside"
        outside.mkdir()
        (self.root / "_build").symlink_to(outside, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlinked _build"):
            scratch.clean(self.root)

    def test_all_targets_are_checked_before_any_deletion(self):
        first = self.root / "_build" / scratch.DIRECTORIES[0]
        first.mkdir(parents=True)
        (self.root / "_build" / scratch.DIRECTORIES[-1]).symlink_to(first)
        with self.assertRaisesRegex(ValueError, "non-directory"):
            scratch.clean(self.root)
        self.assertTrue(first.exists())

    def test_tracked_files_prevent_deletion(self):
        target = self.root / "_build" / scratch.DIRECTORIES[0]
        target.mkdir(parents=True)
        with mock.patch.object(scratch.subprocess, "check_output", return_value=b"tracked\0"):
            with self.assertRaisesRegex(ValueError, "tracked"):
                scratch.clean(self.root)
        self.assertTrue(target.exists())


if __name__ == "__main__":
    unittest.main()
