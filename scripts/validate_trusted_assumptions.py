#!/usr/bin/env python3
"""Audit FIR's explicit Lean trust boundary and pinned upstream source."""

from __future__ import annotations

import hashlib
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.32.0"
EXPECTED_SOURCE_SHA256 = {
    Path("Lean/Compiler/LCNF/AlphaEqv.lean"):
        "f62bf73971d21483f1e285ecc74980bdc12baa0bf5c494fed4dc5d021aeded43",
    Path("Lean/Compiler/LCNF/SimpCase.lean"):
        "270df8851deb0a5f4c6a656377e83e2cf237e76f70a36301239781839122620b",
}
EXPECTED_AXIOMS = {
    (Path("Fir/LeanIR/Passes/AlphaEqvTrusted.lean"), "lean432UpstreamBridge"),
}
AXIOM_RE = re.compile(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE)
PARTIAL_DEF_RE = re.compile(r"^\s*partial\s+def\s+", re.MULTILINE)


def lean_code(text: str) -> str:
    """Replace Lean comments and string contents while preserving newlines."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                output.extend("  ")
                block_depth += 1
                index += 2
            elif text.startswith("-/", index):
                output.extend("  ")
                block_depth -= 1
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            if text[index] == "\\" and index + 1 < len(text):
                output.extend("  ")
                index += 2
            elif text[index] == '"':
                output.append(" ")
                in_string = False
                index += 1
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif text.startswith("--", index):
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
        elif text.startswith("/-", index):
            output.extend("  ")
            block_depth = 1
            index += 2
        elif text[index] == '"':
            output.append(" ")
            in_string = True
            index += 1
        else:
            output.append(text[index])
            index += 1
    return "".join(output)


def upstream_source(relative: Path) -> Path:
    lean = Path(
        subprocess.check_output(["elan", "which", "lean"], text=True).strip()
    )
    return lean.parent.parent / "src/lean" / relative


def main() -> int:
    errors: list[str] = []
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        errors.append(
            f"lean-toolchain is {toolchain!r}, expected {EXPECTED_TOOLCHAIN!r}"
        )

    for relative, expected_digest in EXPECTED_SOURCE_SHA256.items():
        source = upstream_source(relative)
        if not source.is_file():
            errors.append(f"missing pinned upstream source: {source}")
        else:
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            if digest != expected_digest:
                errors.append(
                    f"Lean {relative.name} source hash changed: "
                    f"got {digest}, expected {expected_digest}"
                )

    actual_axioms: set[tuple[Path, str]] = set()
    for path in sorted((ROOT / "Fir").rglob("*.lean")):
        relative = path.relative_to(ROOT)
        code = lean_code(path.read_text(encoding="utf-8"))
        actual_axioms.update((relative, name) for name in AXIOM_RE.findall(code))

    unexpected = actual_axioms - EXPECTED_AXIOMS
    missing = EXPECTED_AXIOMS - actual_axioms
    for path, name in sorted(unexpected):
        errors.append(f"unexpected axiom {name} in {path}")
    for path, name in sorted(missing):
        errors.append(f"missing registered axiom {name} in {path}")

    local = ROOT / "Fir/LeanIR/Passes/AlphaEqvLocal.lean"
    if PARTIAL_DEF_RE.search(lean_code(local.read_text(encoding="utf-8"))):
        errors.append("AlphaEqvLocal must remain total and transparent")

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1

    print(
        "Validated Lean 4.32 AlphaEqv/SimpCase source hashes and exactly one "
        "registered trusted axiom."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
