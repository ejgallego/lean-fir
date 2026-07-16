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
EXPECTED_SOURCE_SHA256 = (
    "f62bf73971d21483f1e285ecc74980bdc12baa0bf5c494fed4dc5d021aeded43"
)
EXPECTED_AXIOMS = {
    (Path("Fir/LeanIR/Passes/AlphaEqvTrusted.lean"), "lean432UpstreamBridge"),
}
AXIOM_RE = re.compile(r"^\s*axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE)
PARTIAL_DEF_RE = re.compile(r"^\s*partial\s+def\s+", re.MULTILINE)


def upstream_source() -> Path:
    lean = Path(
        subprocess.check_output(["elan", "which", "lean"], text=True).strip()
    )
    return (
        lean.parent.parent
        / "src/lean/Lean/Compiler/LCNF/AlphaEqv.lean"
    )


def main() -> int:
    errors: list[str] = []
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        errors.append(
            f"lean-toolchain is {toolchain!r}, expected {EXPECTED_TOOLCHAIN!r}"
        )

    source = upstream_source()
    if not source.is_file():
        errors.append(f"missing pinned upstream source: {source}")
    else:
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if digest != EXPECTED_SOURCE_SHA256:
            errors.append(
                "Lean AlphaEqv source hash changed: "
                f"got {digest}, expected {EXPECTED_SOURCE_SHA256}"
            )

    actual_axioms: set[tuple[Path, str]] = set()
    for path in sorted((ROOT / "Fir").rglob("*.lean")):
        relative = path.relative_to(ROOT)
        text = path.read_text(encoding="utf-8")
        actual_axioms.update((relative, name) for name in AXIOM_RE.findall(text))

    unexpected = actual_axioms - EXPECTED_AXIOMS
    missing = EXPECTED_AXIOMS - actual_axioms
    for path, name in sorted(unexpected):
        errors.append(f"unexpected axiom {name} in {path}")
    for path, name in sorted(missing):
        errors.append(f"missing registered axiom {name} in {path}")

    local = ROOT / "Fir/LeanIR/Passes/AlphaEqvLocal.lean"
    if PARTIAL_DEF_RE.search(local.read_text(encoding="utf-8")):
        errors.append("AlphaEqvLocal must remain total and transparent")

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1

    print(
        "Validated Lean 4.32 AlphaEqv source hash and exactly one registered "
        "trusted axiom."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
