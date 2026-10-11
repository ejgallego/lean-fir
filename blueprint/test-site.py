#!/usr/bin/env python3
"""Focused regression checks for the offline generated-site gate."""

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("check_site", HERE / "check-site.py")
check_site = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check_site)


class SiteTests(unittest.TestCase):
    def setUp(self):
        scratch = HERE.parent / ".deps"
        scratch.mkdir(exist_ok=True)
        temp = tempfile.TemporaryDirectory(prefix="site-test-", dir=scratch)
        self.addCleanup(temp.cleanup)
        self.site = Path(temp.name)
        self.write("index.html", '<a href="chapter/#claim">claim</a>')
        self.write("chapter/index.html", '<base href="../"><h1 id="claim">Claim</h1>'
                   '<script src="asset.js"></script><a href="source.html#L2">source</a>')
        self.write("source.html", '<pre id="L2">source</pre>')
        self.write("asset.js", "// asset")
        self.write("find/index.html", "<p>Native lookup</p>")
        self.write("xref.json", json.dumps({"Verso.Genre.Manual.section": {"contents": {
            "claim": [{"address": "/chapter/", "id": "claim"}]}}}))

    def write(self, relative, text):
        path = self.site / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def test_nested_pages_and_assets_under_project_prefix(self):
        errors, counts = check_site.check(self.site, "/lean-fir/")
        self.assertEqual(errors, [])
        self.assertEqual(counts["htmlFiles"], 4)

    def test_missing_file_and_fragment_fail(self):
        self.write("index.html", '<a href="missing/">missing</a>'
                   '<a href="source.html#absent">absent</a>')
        (self.site / "asset.js").unlink()
        errors, _ = check_site.check(self.site)
        self.assertTrue(any("missing local target" in e for e in errors))
        self.assertTrue(any("missing fragment" in e for e in errors))
        self.assertTrue(any("asset.js" in e for e in errors))

    def test_root_absolute_link_escapes_project_prefix(self):
        self.write("index.html", '<a href="/chapter/#claim">claim</a>')
        self.assertEqual(check_site.check(self.site)[0], [])
        self.assertTrue(any("escapes project base" in e
                            for e in check_site.check(self.site, "/lean-fir/")[0]))

    def test_compatibility_document_resolves_native_lookup(self):
        self.write("index.html", "<p>Home</p>")
        self.write("old/index.html", '<meta http-equiv="refresh" '
                   'content="0; url=../find/?domain=Verso.Genre.Manual.section&amp;name=claim">'
                   '<a href="../find/?domain=Verso.Genre.Manual.section&amp;name=claim">Claim</a>')
        errors, counts = check_site.check(self.site, "/lean-fir/")
        self.assertEqual(errors, [])
        self.assertEqual(counts["nativeLookups"], 1)
        self.write("chapter/index.html", '<h1 id="other">Other</h1>')
        self.assertTrue(any("missing fragment" in e
                            for e in check_site.check(self.site, "/lean-fir/")[0]))

    def test_missing_native_lookup_fails(self):
        self.write("index.html", '<a href="find/?domain=Verso.Genre.Manual.section&amp;name=absent">Absent</a>')
        self.assertTrue(any("missing native lookup" in e
                            for e in check_site.check(self.site)[0]))


if __name__ == "__main__":
    unittest.main()
