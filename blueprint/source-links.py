#!/usr/bin/env python3
"""Emit local source pages from typed source records captured by the generator.

This consumes this project's own input format, not VBP's serialized caches.
Ordinary Lake builds establish import freshness; these are snapshots from this
documentation build, checked for mutations between capture and emission.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
from pathlib import Path
import re
import sys


MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*")
PACKAGE_DIRS = {
    "Fir": Path("Fir"),
    "FirBlueprint": Path("blueprint/FirBlueprint"),
    "FirTalos": Path(".deps/talos-434/project/FirTalos"),
}


def validate(snapshot: dict, output: Path) -> list[dict]:
    root = Path(snapshot["root"]).resolve(strict=True)
    output = output.resolve()
    if not output.is_relative_to(root):
        raise ValueError("source output must remain inside the documentation checkout")
    files = []
    modules = set()
    for item in snapshot["files"]:
        module = item["moduleName"]
        if not isinstance(module, str) or not MODULE.fullmatch(module):
            raise ValueError(f"unsafe source module: {module!r}")
        if module in modules:
            raise ValueError(f"ambiguous source module: {module}")
        modules.add(module)
        components = module.split(".")
        package = components[0]
        if package not in PACKAGE_DIRS or len(components) < 2:
            raise ValueError(f"unsupported associated source package: {module}")
        package_root = (root / PACKAGE_DIRS[package]).resolve(strict=True)
        if not package_root.is_relative_to(root):
            raise ValueError(f"source package escapes the documentation checkout: {package}")
        expected = package_root.joinpath(*components[1:]).with_suffix(".lean")
        path = Path(item["path"]).resolve(strict=True)
        if path != expected or not path.is_relative_to(package_root):
            raise ValueError(f"source path does not match its module: {module}")
        raw = item["text"].encode("utf-8")
        if path.read_bytes() != raw:
            raise ValueError(f"source changed after capture: {module}")
        lines = item["text"].split("\n")
        references = []
        for ref in item["references"]:
            first, last = ref["firstLine"], ref["lastLine"]
            if (type(first) is not int or type(last) is not int
                    or not 1 <= first <= last <= len(lines)):
                raise ValueError(f"invalid source range: {module}:{first}-{last}")
            references.append(dict(ref))
        if not references:
            raise ValueError(f"unreferenced source module: {module}")
        files.append({
            "moduleName": module,
            "package": package,
            "sourcePath": "/".join(components) + ".lean",
            "path": path,
            "raw": raw,
            "lines": lines,
            "references": sorted(references, key=lambda r: (
                r["firstLine"], r["lastLine"], r["declaration"])),
            "sha256": hashlib.sha256(raw).hexdigest(),
        })
    return sorted(files, key=lambda f: f["moduleName"])


def source_page(file: dict, snapshot: dict) -> str:
    module = file["moduleName"]
    anchors: dict[int, set[str]] = {}
    for ref in file["references"]:
        anchors.setdefault(ref["firstLine"], set()).add(
            f'L{ref["firstLine"]}-L{ref["lastLine"]}')
    body = []
    for number, line in enumerate(file["lines"], 1):
        for anchor in sorted(anchors.get(number, ())):
            body.append(f'<span class="range-anchor" id="{anchor}"></span>')
        body.append(
            f'<span class="line" id="L{number}"><a class="number" '
            f'href="#L{number}">{number}</a><code>{html.escape(line, quote=False)}</code></span>')
    revision = html.escape(snapshot["revision"][:10])
    state = " with working-tree changes" if snapshot["workingTreeChanges"] else ""
    overlay = " (documentation overlay)" if file["package"] == "FirTalos" else ""
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width">
<title>{module} — source</title><style>
body{{margin:2rem;font:16px system-ui,sans-serif;color:#1f2937;background:#fff}}
header{{margin-bottom:1.5rem}}pre{{overflow:auto;font:14px/1.5 ui-monospace,monospace}}
.line{{display:block;min-height:1.5em}}.number{{display:inline-block;width:5em;
text-align:right;padding-right:1.5em;color:#64748b;text-decoration:none;user-select:none}}
.line:target,.range-anchor:target+.line{{background:#fef3c7}}
.range-anchor{{display:block;scroll-margin-top:1rem}}code{{white-space:pre}}
</style></head><body><header><h1>{module}</h1>
<p>{html.escape(file["sourcePath"])}{overlay}</p>
<p>Source snapshot from this documentation build. Checkout {revision}{state}.</p>
<p><a href="{module}.lean">Download source</a></p></header>
<pre>{"".join(body)}</pre></body></html>
'''


def emit(snapshot: dict, output: Path) -> list[dict]:
    files = validate(snapshot, output)
    destination = output.resolve() / "source"
    if destination.exists() and (destination.is_symlink() or not destination.is_dir()):
        raise ValueError("source output directory must be a regular directory")
    destination.mkdir(parents=True, exist_ok=True)
    inventory = []
    for file in files:
        module = file["moduleName"]
        # Reject output symlinks rather than overwriting unrelated files.
        for suffix in (".html", ".lean"):
            if (destination / (module + suffix)).is_symlink():
                raise ValueError(f"source output is a symlink: {module}{suffix}")
        (destination / (module + ".html")).write_text(
            source_page(file, snapshot), encoding="utf-8")
        (destination / (module + ".lean")).write_bytes(file["raw"])
        inventory.append({key: file[key] for key in (
            "moduleName", "package", "sourcePath", "sha256", "references")})
    index = destination / "sources.json"
    if index.is_symlink():
        raise ValueError("source inventory is a symlink")
    index.write_text(json.dumps({
        "schemaVersion": "fir.blueprint.source-snapshots/v1",
        "revision": snapshot["revision"],
        "workingTreeChanges": snapshot["workingTreeChanges"],
        "files": inventory,
    }, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return inventory


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        emit(json.load(sys.stdin), args.output)
    except (KeyError, OSError, TypeError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
