#!/usr/bin/env python3
"""Validate FIR's deliberately small, textual bug-card format."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BUGS = ROOT / "bugs"
TEMPLATE = BUGS / "_template.md"

REQUIRED_FIELDS = (
    "id",
    "status",
    "classification",
    "lean-toolchain",
    "lean-revision",
    "phase",
    "pass",
    "discovered-by",
    "first-seen",
    "reproduction",
    "regression",
)
REQUIRED_HEADINGS = (
    "# Summary",
    "## Minimal reproduction",
    "## Exact commands",
    "## Expected semantics",
    "## Actual behavior",
    "## Proof or differential evidence",
    "## Semantic impact",
    "## Classification and triage",
    "## Workaround",
    "## Upstream tracking",
    "## Resolution and regression",
)
STATUSES = {"candidate", "confirmed", "upstreamed", "fixed", "closed-not-a-bug"}
CLASSIFICATIONS = {
    "compiler",
    "fir-semantics",
    "validation-harness",
    "wasm-adapter",
    "upstream-drift",
}
ID_RE = re.compile(r"FIR-BUG-[A-Za-z0-9][A-Za-z0-9._-]*\Z")
DATE_RE = re.compile(r"\d{4}-\d{2}-\d{2}\Z")


def parse_card(path: Path) -> tuple[dict[str, str], str]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    if not lines or lines[0] != "---":
        raise ValueError("missing opening YAML delimiter")
    try:
        end = lines.index("---", 1)
    except ValueError as exc:
        raise ValueError("missing closing YAML delimiter") from exc

    fields: dict[str, str] = {}
    for number, line in enumerate(lines[1:end], start=2):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        key, separator, value = line.partition(":")
        if not separator or not key.strip() or not value.strip():
            raise ValueError(f"invalid frontmatter line {number}")
        key = key.strip()
        if key in fields:
            raise ValueError(f"duplicate frontmatter field {key!r}")
        fields[key] = value.strip()
    return fields, "\n".join(lines[end + 1 :])


def local_target(value: str) -> Path | None:
    if value in {"none", "unresolved"} or value.startswith(("http://", "https://")):
        return None
    return ROOT / value.split("#", 1)[0]


def validate(path: Path, ids: set[str]) -> list[str]:
    errors: list[str] = []
    try:
        fields, body = parse_card(path)
    except ValueError as exc:
        return [f"{path.relative_to(ROOT)}: {exc}"]

    for field in REQUIRED_FIELDS:
        if field not in fields:
            errors.append(f"missing field {field!r}")
    for heading in REQUIRED_HEADINGS:
        if heading not in body.splitlines():
            errors.append(f"missing heading {heading!r}")

    if path != TEMPLATE and all(field in fields for field in REQUIRED_FIELDS):
        card_id = fields["id"]
        if not ID_RE.fullmatch(card_id):
            errors.append(f"invalid id {card_id!r}")
        elif card_id in ids:
            errors.append(f"duplicate id {card_id!r}")
        else:
            ids.add(card_id)
        if path.stem != card_id:
            errors.append(f"filename must be {card_id}.md")
        if fields["status"] not in STATUSES:
            errors.append(f"invalid status {fields['status']!r}")
        if fields["classification"] not in CLASSIFICATIONS:
            errors.append(f"invalid classification {fields['classification']!r}")
        if not DATE_RE.fullmatch(fields["first-seen"]):
            errors.append("first-seen must have YYYY-MM-DD form")
        for field in ("reproduction", "regression"):
            target = local_target(fields[field])
            if target is not None and not target.exists():
                errors.append(f"{field} target does not exist: {fields[field]}")
        if fields["status"] == "fixed" and fields["regression"] == "none":
            errors.append("fixed cards must name a regression test")

    prefix = f"{path.relative_to(ROOT)}: "
    return [prefix + error for error in errors]


def main() -> int:
    cards = sorted(BUGS.glob("*.md"))
    ids: set[str] = set()
    errors = [error for path in cards if path.name != "README.md" for error in validate(path, ids)]
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    active = sum(path.name not in {"README.md", "_template.md"} for path in cards)
    print(f"Validated FIR bug-card template and {active} active card(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
