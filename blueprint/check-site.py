#!/usr/bin/env python3
"""Check generated HTML targets, linked assets and native section lookups offline."""

import argparse
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from urllib.parse import parse_qs, unquote, urljoin, urlparse


class Page(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.base = None
        self.ids = set()
        self.links = []
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        if tag == "a" and "name" in attrs:
            self.ids.add(attrs["name"])
        if tag == "base":
            if self.base is None:
                self.base = attrs.get("href")
            return
        for key in ("href", "src"):
            if attrs.get(key):
                self.links.append(attrs[key])
        if tag == "meta" and attrs.get("http-equiv", "").lower() == "refresh":
            match = re.fullmatch(r"\s*\d+(?:\.\d+)?\s*;\s*url\s*=\s*(.*?)\s*",
                                 attrs.get("content", ""), re.IGNORECASE)
            if match:
                self.links.append(match[1].strip("\"'"))


def check(site, base_path="/"):
    site = Path(site).resolve()
    if not (site / "index.html").is_file():
        return ["missing site index.html"], {}
    base_path = "/" + base_path.strip("/") + "/" if base_path.strip("/") else "/"
    origin = "https://blueprint.invalid"
    site_url = origin + base_path
    pages = {p.relative_to(site).as_posix(): Page(p.read_text(encoding="utf-8"))
             for p in site.rglob("*.html")}
    xref_path = site / "xref.json"
    xrefs = json.loads(xref_path.read_text(encoding="utf-8")) if xref_path.is_file() else {}
    errors = set()
    targets = set()
    lookups = set()

    def target(url, source):
        parsed = urlparse(url)
        if parsed.scheme not in ("http", "https") or parsed.netloc != "blueprint.invalid":
            return
        path = unquote(parsed.path)
        if not path.startswith(base_path):
            errors.add(f"{source}: target escapes project base {base_path}: {url}")
            return
        relative = path[len(base_path):]
        if not relative or relative.endswith("/"):
            relative += "index.html"
        file = (site / relative).resolve()
        if not file.is_relative_to(site) or not file.is_file():
            errors.add(f"{source}: missing local target: {url}")
            return
        targets.add(url)
        fragment = unquote(parsed.fragment)
        if fragment and relative in pages and fragment not in pages[relative].ids:
            errors.add(f"{source}: missing fragment: {url}")
        if relative == "find/index.html":
            query = parse_qs(parsed.query)
            if "domain" in query and "name" in query:
                domain, name = query["domain"][0], query["name"][0]
                if (domain, name) in lookups:
                    return
                lookups.add((domain, name))
                entries = xrefs.get(domain, {}).get("contents", {}).get(name, [])
                if not entries:
                    errors.add(f"{source}: missing native lookup: {domain}/{name}")
                for entry in entries:
                    # Native xref addresses are relative to the site root,
                    # including when the site is hosted under a project prefix.
                    destination = urljoin(site_url, entry["address"].lstrip("/"))
                    target(destination + "#" + entry["id"], source)

    for relative, page in pages.items():
        page_url = urljoin(site_url, relative)
        base = urljoin(page_url, page.base) if page.base is not None else page_url
        for link in page.links:
            target(urljoin(base, link), relative)
    return sorted(errors), {"htmlFiles": len(pages), "localTargets": len(targets),
                            "nativeLookups": len(lookups), "basePath": base_path}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    parser.add_argument("--base-path", default="/")
    args = parser.parse_args()
    errors, counts = check(args.site, args.base_path)
    for error in errors:
        print(error)
    print(json.dumps({"ok": not errors, **counts, "errors": len(errors)}, sort_keys=True))
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
