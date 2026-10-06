#!/usr/bin/env python3
"""Focused checks for source identity, path constraints and portable links."""

import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from urllib.parse import urljoin

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("source_links", HERE / "source-links.py")
source_links = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source_links)


class SourceLinksTests(unittest.TestCase):
    def setUp(self):
        scratch = HERE.parent / ".deps"
        scratch.mkdir(exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(prefix="source-link-test-", dir=scratch)
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.path = self.root / "blueprint/FirBlueprint/Targets/Example.lean"
        self.path.parent.mkdir(parents=True)
        self.text = '-- <script>alert("escaped")</script> & source\nnamespace Example\nend Example\n'
        self.path.write_text(self.text, encoding="utf-8")
        self.output = self.root / "blueprint/_out/site/html-multi"
        self.snapshot = {
            "root": str(self.root), "revision": "0123456789abcdef", "workingTreeChanges": True,
            "files": [{
                "moduleName": "FirBlueprint.Targets.Example", "path": str(self.path),
                "text": self.text, "references": [{
                    "declaration": "Example.test", "firstLine": 2, "lastLine": 3}],
            }],
        }

    def test_exact_source_escape_and_range_anchors(self):
        source_links.emit(self.snapshot, self.output)
        page = (self.output / "source/FirBlueprint.Targets.Example.html").read_text()
        self.assertIn('id="L2-L3"', page)
        self.assertIn('id="L2"', page)
        self.assertIn('&lt;script&gt;alert("escaped")&lt;/script&gt; &amp; source', page)
        self.assertNotIn('<script>', page)
        self.assertNotIn(str(self.root), page)
        self.assertEqual((self.output / "source/FirBlueprint.Targets.Example.lean").read_bytes(),
                         self.path.read_bytes())
        index = json.loads((self.output / "source/sources.json").read_text())
        self.assertNotIn(str(self.root), json.dumps(index))

    def test_rejects_source_mutation_after_capture(self):
        self.path.write_text(self.text + "-- changed\n")
        with self.assertRaisesRegex(ValueError, "changed after capture"):
            source_links.emit(self.snapshot, self.output)
        self.assertFalse(self.output.exists())

    def test_rejects_missing_source(self):
        self.path.unlink()
        with self.assertRaises(FileNotFoundError):
            source_links.emit(self.snapshot, self.output)

    def test_rejects_module_and_source_path_traversal(self):
        for module in ("../outside", "FirBlueprint/Targets/Example", "FirBlueprint..Example"):
            snapshot = copy.deepcopy(self.snapshot)
            snapshot["files"][0]["moduleName"] = module
            with self.subTest(module=module), self.assertRaises(ValueError):
                source_links.emit(snapshot, self.output)
        snapshot = copy.deepcopy(self.snapshot)
        snapshot["files"][0]["path"] = str(HERE / "source-links.py")
        with self.assertRaisesRegex(ValueError, "does not match"):
            source_links.emit(snapshot, self.output)

    def test_rejects_invalid_ranges_and_collisions(self):
        for first, last in ((0, 2), (3, 2), (1, 99), (True, 2)):
            snapshot = copy.deepcopy(self.snapshot)
            snapshot["files"][0]["references"][0].update(firstLine=first, lastLine=last)
            with self.subTest(first=first, last=last), self.assertRaisesRegex(ValueError, "range"):
                source_links.emit(snapshot, self.output)
        snapshot = copy.deepcopy(self.snapshot)
        snapshot["files"].append(copy.deepcopy(snapshot["files"][0]))
        with self.assertRaisesRegex(ValueError, "ambiguous"):
            source_links.emit(snapshot, self.output)

    def test_rejects_source_package_symlink_escape(self):
        outside = tempfile.TemporaryDirectory(prefix="source-link-outside-", dir=self.root.parent)
        self.addCleanup(outside.cleanup)
        namespace = self.root / "blueprint/FirBlueprint"
        moved = Path(outside.name) / "FirBlueprint"
        namespace.rename(moved)
        namespace.symlink_to(moved, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "package escapes"):
            source_links.emit(self.snapshot, self.output)

    def test_rejects_output_escape_and_symlink(self):
        with self.assertRaisesRegex(ValueError, "inside"):
            source_links.emit(self.snapshot, self.root.parent / "outside")
        self.output.mkdir(parents=True)
        (self.output / "source").symlink_to(self.path.parent, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "regular directory"):
            source_links.emit(self.snapshot, self.output)

    def test_nested_and_hosted_subpath_resolution(self):
        href = "source/FirBlueprint.Targets.Example.html#L2-L3"
        site = "https://example.org/fir/docs/"
        nested = site + "W6/Open-proof-frontier/index.html"
        base = urljoin(nested, "../../")
        self.assertEqual(urljoin(base, href), site + href)
        # API clients resolve sourceHref against the same canonical site base
        # used for existing manifest entry hrefs.
        self.assertEqual(urljoin(site, href), site + href)


if __name__ == "__main__":
    unittest.main()
