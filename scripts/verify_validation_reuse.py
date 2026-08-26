#!/usr/bin/env python3
"""Fail-closed reuse of one exact FIR validation evidence receipt."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Callable

from validation_harness import (
    BuildContext,
    ValidationBuildInput,
    ValidationError,
    canonical_build_input_manifest_bytes,
    corpus_artifact_bytes,
    regular_file_content_without_symlinks,
    resolve_lake_command,
    select_cases,
    sha256_bytes,
    validation_plan_from_config,
    verify_evidence_receipt,
)
from validate_interpreters import NATIVE_ADAPTER, corpus_manifest
from validation_lcnf import prepare_manifest as prepare_lcnf_manifest


ROOT = Path(__file__).resolve().parents[1]


def checked_file_digest(path: Path, context: str) -> str:
    return sha256_bytes(regular_file_content_without_symlinks(path, context))


def require_file_identity(
    expected: str, candidates: list[Path], context: str
) -> Path:
    checked: list[tuple[Path, str]] = []
    for candidate in candidates:
        absolute = Path(os.path.abspath(candidate))
        if any(path == absolute for path, _ in checked):
            continue
        try:
            digest = checked_file_digest(absolute, context)
        except ValidationError:
            continue
        checked.append((absolute, digest))
        if digest == expected:
            return absolute
    observed = ", ".join(f"{path}={digest}" for path, digest in checked)
    raise ValidationError(
        f"{context} no longer matches retained sha256 {expected}"
        + (f"; observed {observed}" if observed else "; no current file")
    )


def command_path(name: str, context: str) -> Path:
    resolved = shutil.which(name)
    if resolved is None:
        raise ValidationError(f"{context}: cannot resolve command {name}")
    return Path(resolved).resolve()


def tool_candidates(root: Path, lean: Path, name: str) -> list[Path]:
    if name in {"lean-toolchain/bin/lean", "bin/lean"}:
        return [lean]
    if name == "lake":
        return [lean.with_name("lake")]
    if name in {"bwrap", "node", "strace"}:
        return [command_path(name, f"validation reuse tool {name}")]
    return [root / name]


def olean_candidates(root: Path, lean: Path, name: str) -> list[Path]:
    lean_prefix = lean.parent.parent
    return [
        root / ".lake" / "build" / "lib" / "lean" / name,
        lean_prefix / "lib" / "lean" / name,
    ]


def verify_current_inputs(matrix: dict, root: Path) -> None:
    for item in matrix["inputs"]:
        if item["kind"] == "corpus":
            continue
        name = item["name"]
        if name.startswith("external/"):
            raise ValidationError(
                "validation reuse does not guess a current path for an "
                f"external input: {name}"
            )
        require_file_identity(
            item["sha256"],
            [root / name],
            f"validation reuse input {item['kind']}:{name}",
        )


def verify_current_tools(matrix: dict, root: Path, lean: Path) -> None:
    for item in matrix["tools"]:
        require_file_identity(
            item["sha256"],
            tool_candidates(root, lean, item["name"]),
            "validation reuse tool "
            f"{item['backend']}:{item['kind']}:{item['name']}",
        )


def verify_current_build_inputs(matrix: dict, root: Path, lean: Path) -> None:
    by_backend: dict[str, list[dict]] = {}
    for item in matrix["buildInputs"]:
        by_backend.setdefault(item["backend"], []).append(item)
    for backend, items in by_backend.items():
        manifests = [
            item for item in items if item["kind"] == "build-input-manifest"
        ]
        members = [
            item for item in items if item["kind"] != "build-input-manifest"
        ]
        if len(manifests) != 1 or not members:
            raise ValidationError(
                f"validation reuse build inputs for {backend} are incomplete"
            )
        current: list[ValidationBuildInput] = []
        for item in members:
            kind = item["kind"]
            name = item["name"]
            if kind == "lean-compiler":
                candidates = [lean]
            elif kind == "lean-olean":
                candidates = olean_candidates(root, lean, name)
            else:
                raise ValidationError(
                    f"validation reuse has no resolver for build input "
                    f"{backend}:{kind}:{name}"
                )
            path = require_file_identity(
                item["sha256"],
                candidates,
                f"validation reuse build input {backend}:{kind}:{name}",
            )
            current.append(
                ValidationBuildInput(
                    backend,
                    kind,
                    name,
                    item["sha256"],
                    source_path=path,
                )
            )
        manifest = canonical_build_input_manifest_bytes(tuple(current))
        if sha256_bytes(manifest) != manifests[0]["sha256"]:
            raise ValidationError(
                f"validation reuse build-input manifest changed for {backend}"
            )


def verify_plan_coverage(
    matrix: dict, descriptors: list[dict], plan_path: Path, root: Path = ROOT
) -> None:
    plan = validation_plan_from_config(plan_path)
    if plan.corpus_backend != "native":
        raise ValidationError(
            "validation reuse currently requires the native corpus backend"
        )
    expected_cases = select_cases(descriptors, None, None, plan.exclude_tags)
    if matrix["selectedCases"] != expected_cases:
        raise ValidationError(
            "validation reuse selection does not exactly cover the requested "
            "plan"
        )
    retained_pairs = {
        (item["reference"], item["candidate"]) for item in matrix["pairs"]
    }
    missing_pairs = sorted(set(plan.pairs) - retained_pairs)
    if missing_pairs:
        raise ValidationError(
            "validation reuse is missing requested comparison pair(s): "
            + ", ".join(f"{left}:{right}" for left, right in missing_pairs)
        )
    retained_inputs = {
        (item["kind"], item["name"], item["sha256"])
        for item in matrix["inputs"]
    }
    for kind, paths in (
        ("adapter-config", plan.adapter_configs),
        ("provider-config", plan.provider_configs),
    ):
        for path in paths:
            try:
                name = path.resolve().relative_to(root).as_posix()
            except ValueError as error:
                raise ValidationError(
                    "validation reuse cannot bind an external requested config"
                ) from error
            digest = checked_file_digest(path.resolve(), f"requested {kind}")
            if (kind, name, digest) not in retained_inputs:
                raise ValidationError(
                    f"validation reuse is missing requested {kind} {name}"
                )


def verify_reusable_receipt(
    receipt_path: Path, plan_path: Path, root: Path = ROOT
) -> dict:
    source = verify_evidence_receipt(receipt_path)
    matrix = source.matrix
    verify_current_inputs(matrix, root)
    lean = resolve_lake_command(root, "lean").resolve()
    verify_current_tools(matrix, root, lean)
    verify_current_build_inputs(matrix, root, lean)

    NATIVE_ADAPTER.build(BuildContext(root, receipt_path.parent, True))
    # The normal matrix path asks every participating adapter to prepare the
    # corpus after the corpus owner has supplied it. Mirror the LCNF adapter's
    # second canonicalization exactly before comparing the retained corpus.
    descriptors = prepare_lcnf_manifest(corpus_manifest())
    corpus = corpus_artifact_bytes(descriptors)
    retained_corpus = matrix["inputs"][0]
    if (
        retained_corpus["kind"] != "corpus"
        or retained_corpus["name"] != "corpus.json"
        or retained_corpus["sha256"] != sha256_bytes(corpus)
    ):
        raise ValidationError(
            "validation reuse corpus no longer matches retained evidence"
        )
    verify_plan_coverage(matrix, descriptors, plan_path, root)
    return matrix


def ensure_reusable_receipt(
    receipt_path: Path,
    plan_path: Path,
    rerun: Callable[[], None],
    root: Path = ROOT,
) -> tuple[dict, bool]:
    try:
        return verify_reusable_receipt(receipt_path, plan_path, root), False
    except ValidationError as error:
        print(
            f"validation receipt is not reusable ({error}); rerunning",
            file=sys.stderr,
        )
    rerun()
    return verify_reusable_receipt(receipt_path, plan_path, root), True


def rerun_v8_validation(root: Path = ROOT) -> None:
    try:
        subprocess.run(
            ["make", "-C", str(root), "validate-v8"],
            check=True,
        )
    except subprocess.CalledProcessError as error:
        raise ValidationError(
            f"validation-v8 rerun failed with status {error.returncode}"
        ) from error


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="verify exact FIR validation evidence for reuse"
    )
    parser.add_argument("--receipt", required=True, type=Path)
    parser.add_argument("--plan", required=True, type=Path)
    parser.add_argument(
        "--rerun-v8-on-mismatch",
        action="store_true",
        help="rerun make validate-v8, then reverify, when reuse fails",
    )
    args = parser.parse_args(argv)
    reran = False
    if args.rerun_v8_on_mismatch:
        matrix, reran = ensure_reusable_receipt(
            args.receipt,
            args.plan,
            rerun_v8_validation,
        )
    else:
        matrix = verify_reusable_receipt(args.receipt, args.plan)
    pairs = {(item["reference"], item["candidate"]) for item in matrix["pairs"]}
    requested = validation_plan_from_config(args.plan).pairs
    print(
        f"verified reusable validation receipt {args.receipt}: "
        f"{len(matrix['selectedCases'])} cases, "
        f"{len(requested)}/{len(pairs)} requested comparison pairs, "
        f"execution={'rerun' if reran else 'reused'}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validation reuse error: {error}", file=sys.stderr)
        raise SystemExit(2)
