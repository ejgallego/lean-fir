#!/usr/bin/env python3
"""Audit maintained FIR proof sources and force the compiled W6 endpoint gate."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import runpy
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
# Reuse the comment/string-aware lexer and the existing project-axiom registry.
SOURCE_AUDIT = runpy.run_path(str(ROOT / "scripts/validate_trusted_assumptions.py"))
LEAN_CODE = SOURCE_AUDIT["lean_code"]
EXPECTED_AXIOMS = SOURCE_AUDIT["EXPECTED_AXIOMS"]
AXIOM = re.compile(
    r"^\s*(?:(?:private|protected|public|noncomputable)\s+)*"
    r"axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE
)
PLACEHOLDER = re.compile(r"\b(?:sorry|admit)\b")
PROOF_ROOTS = ("Fir", "Inspect", "integration/talos/FirTalos")


def source_files(root: Path) -> list[Path]:
    files = set(root.glob("*.lean"))
    files.update((root / "integration/talos").glob("*.lean"))
    for relative in PROOF_ROOTS:
        files.update((root / relative).rglob("*.lean"))
    return sorted(files)


def audit_sources(root: Path) -> tuple[list[str], int]:
    errors: list[str] = []
    actual: set[tuple[Path, str]] = set()
    files = source_files(root)
    for path in files:
        relative = path.relative_to(root)
        code = LEAN_CODE(path.read_text(encoding="utf-8"))
        actual.update((relative, name) for name in AXIOM.findall(code))
        for match in PLACEHOLDER.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            errors.append(f"proof placeholder in {relative}:{line}")
    for path, name in sorted(actual - EXPECTED_AXIOMS):
        errors.append(f"unexpected textual axiom {name} in {path}")
    for path, name in sorted(EXPECTED_AXIOMS - actual):
        errors.append(f"missing registered axiom {name} in {path}")
    return errors, len(files)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources-only", action="store_true")
    options = parser.parse_args()
    errors, count = audit_sources(ROOT)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Source trust audit: {count} Lean files, including Talos integration; pass.", flush=True)
    if options.sources_only:
        return 0
    env = os.environ.copy()
    env["LAKE_CACHE_DIR"] = subprocess.check_output(
        ["bash", str(ROOT / "scripts/fir-lake-cache-path.sh")], cwd=ROOT, text=True
    ).strip()
    env["LAKE_ARTIFACT_CACHE"] = "true"
    env["LAKE_RESTORE_ARTIFACTS"] = "true"
    scratch = ROOT / ".deps/proof-trust/tmp"
    scratch.mkdir(parents=True, exist_ok=True)
    env["TMPDIR"] = str(scratch)
    project = ROOT / "integration/talos"
    # Refresh the dependency cone before forcing the audit itself. This prevents
    # a stale audit olean from turning the gate green without checking endpoints.
    subprocess.run(
        ["lake", "build", "FirTalos.TrustAudit"], cwd=project, env=env, check=True
    )
    return subprocess.run(
        ["lake", "env", "lean", "FirTalos/TrustAudit.lean"], cwd=project, env=env
    ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
