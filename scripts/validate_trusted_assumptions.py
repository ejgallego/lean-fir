#!/usr/bin/env python3
"""Audit FIR's explicit Lean trust boundary and pinned upstream source."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PROFILE = "lean-4.33"


@dataclass(frozen=True)
class AuditProfile:
    pin: str
    version: str
    githash: str


AUDIT_PROFILES = {
    DEFAULT_PROFILE: AuditProfile(
        pin="leanprover/lean4:v4.33.0",
        version="4.33.0",
        githash="d8b18978322de05a8f3dba51ef03cf5461676c17",
    ),
    "lean-4.34-rc2": AuditProfile(
        pin="leanprover/lean4:v4.34.0-rc2",
        version="4.34.0-rc2",
        githash="6a10ac8c22beadecabdbb0919c2b50214762f91d",
    ),
}
EXPECTED_SOURCE_SHA256 = {
    Path("Lean/Compiler/LCNF/AlphaEqv.lean"):
        "f62bf73971d21483f1e285ecc74980bdc12baa0bf5c494fed4dc5d021aeded43",
    Path("Lean/Compiler/LCNF/Basic.lean"):
        "9f86cfac11a407fd0300259723aff0e8f831c7e08eccede4e471c4332f2e6f0b",
    Path("Lean/Compiler/LCNF/SimpCase.lean"):
        "270df8851deb0a5f4c6a656377e83e2cf237e76f70a36301239781839122620b",
    Path("Lean/Compiler/LCNF/ElimDead.lean"):
        "c5a22e15eab79ebd6ef1e8f302095c69aeaccb12275f7468b505b03cde97a582",
}
EXPECTED_LOCAL_SOURCE_SHA256 = {
    Path("Fir/LeanIR/Passes/AlphaEqvLocal.lean"):
        "ba2aa311403cb41f10a0db263f8cd159b498f5927045d0bea8088a79b3d7cf09",
    Path("Fir/LeanIR/Passes/AlphaEqvTrusted.lean"):
        "add1b977f94c00ecf40c5e244d4a7618cd998aed52a3c60720cfefbb1cef0f27",
}
EXPECTED_AXIOMS = {
    (Path("Fir/LeanIR/Passes/AlphaEqvTrusted.lean"), "lean433UpstreamBridge"),
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


LEAN_VERSION_RE = re.compile(
    r"^Lean \(version ([^,]+), [^,]+, commit ([0-9a-f]{40}), Release\)$"
)


def select_profile(pin: str, version: str, githash: str) -> str | None:
    matches = [
        name for name, profile in AUDIT_PROFILES.items()
        if (profile.pin, profile.version, profile.githash) == (pin, version, githash)
    ]
    return matches[0] if len(matches) == 1 else None


def resolve_lean(project: Path) -> tuple[Path, str, str]:
    env = os.environ.copy()
    env.pop("ELAN_TOOLCHAIN", None)
    lean = Path(subprocess.check_output(
        ["elan", "which", "lean"], cwd=project, env=env, text=True
    ).strip())
    output = subprocess.check_output([lean, "--version"], text=True).strip()
    match = LEAN_VERSION_RE.fullmatch(output)
    if match is None:
        raise ValueError(f"unrecognized Lean identity: {output!r}")
    return lean, match.group(1), match.group(2)


def audit_hashes(
    base: Path, expected_hashes: dict[Path, str], label: str
) -> list[str]:
    errors: list[str] = []
    for relative, expected_digest in expected_hashes.items():
        source = base / relative
        if not source.is_file():
            errors.append(f"missing {label} source: {source}")
            continue
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        if digest != expected_digest:
            errors.append(
                f"{label} source hash changed for {relative}: "
                f"got {digest}, expected {expected_digest}"
            )
    return errors


def audit_axioms(root: Path) -> list[str]:
    actual_axioms: set[tuple[Path, str]] = set()
    for path in sorted((root / "Fir").rglob("*.lean")):
        relative = path.relative_to(root)
        code = lean_code(path.read_text(encoding="utf-8"))
        actual_axioms.update((relative, name) for name in AXIOM_RE.findall(code))

    errors: list[str] = []
    for path, name in sorted(actual_axioms - EXPECTED_AXIOMS):
        errors.append(f"unexpected axiom {name} in {path}")
    for path, name in sorted(EXPECTED_AXIOMS - actual_axioms):
        errors.append(f"missing registered axiom {name} in {path}")
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--profile", choices=sorted(AUDIT_PROFILES), default=DEFAULT_PROFILE
    )
    parser.add_argument(
        "--lean-project", type=Path,
        help="project whose tracked lean-toolchain selects the audited compiler",
    )
    options = parser.parse_args(argv)
    errors: list[str] = []
    if options.profile != DEFAULT_PROFILE and options.lean_project is None:
        errors.append(f"profile {options.profile!r} requires --lean-project")
    project = (options.lean_project or ROOT).resolve()
    toolchain_file = project / "lean-toolchain"
    if not toolchain_file.is_file():
        errors.append(f"missing audited project toolchain: {toolchain_file}")
        toolchain = ""
    else:
        toolchain = toolchain_file.read_text(encoding="utf-8").strip()
    expected_profile = AUDIT_PROFILES[options.profile]
    if toolchain != expected_profile.pin:
        errors.append(
            f"lean-toolchain is {toolchain!r}, expected {expected_profile.pin!r}"
        )

    lean: Path | None = None
    version = ""
    githash = ""
    if not errors:
        try:
            lean, version, githash = resolve_lean(project)
        except (OSError, subprocess.CalledProcessError, ValueError) as error:
            errors.append(f"cannot authenticate Lean compiler: {error}")
    selected = select_profile(toolchain, version, githash) if lean is not None else None
    if lean is not None and selected != options.profile:
        errors.append(
            "unreviewed Lean identity: "
            f"pin={toolchain!r}, version={version!r}, githash={githash!r}"
        )

    if lean is not None:
        errors.extend(audit_hashes(
            lean.parent.parent / "src/lean", EXPECTED_SOURCE_SHA256, "Lean"
        ))
    errors.extend(audit_hashes(ROOT, EXPECTED_LOCAL_SOURCE_SHA256, "local audited"))
    errors.extend(audit_axioms(ROOT))

    local = ROOT / "Fir/LeanIR/Passes/AlphaEqvLocal.lean"
    if PARTIAL_DEF_RE.search(lean_code(local.read_text(encoding="utf-8"))):
        errors.append("AlphaEqvLocal must remain total and transparent")

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1

    print(
        f"Validated {options.profile} AlphaEqv/Basic/SimpCase/ElimDead and local "
        "checker source hashes with exactly one registered textual alpha-bridge "
        "axiom under Fir/. The legacy lean433UpstreamBridge name intentionally "
        "identifies the retained audited assumption for both reviewed compilers; "
        "this compatibility audit is not a kernel proof of its universal proposition. "
        "Generated endpoint dependencies are checked separately by make proof-trust."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
