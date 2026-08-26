#!/usr/bin/env python3
"""Record or verify one exact successful FIR Talos build."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "fir-talos-build-attestation/v1"


class AttestationError(Exception):
    pass


def canonical_bytes(value: object) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode("utf-8")


def file_record(
    root: Path, path: Path, logical_path: str | None = None
) -> dict[str, object]:
    absolute = Path(os.path.abspath(path))
    if logical_path is None:
        try:
            relative = absolute.relative_to(root).as_posix()
        except ValueError as error:
            raise AttestationError(f"Talos build path escapes FIR root: {path}") from error
    else:
        relative = logical_path
    try:
        stat = absolute.lstat()
    except OSError as error:
        raise AttestationError(f"cannot inspect Talos build path {relative}: {error}") from error
    if absolute.is_symlink() or not absolute.is_file():
        raise AttestationError(f"Talos build path is not a regular file: {relative}")
    digest = hashlib.sha256()
    try:
        with absolute.open("rb") as source:
            while block := source.read(1024 * 1024):
                digest.update(block)
    except OSError as error:
        raise AttestationError(f"cannot read Talos build path {relative}: {error}") from error
    return {"path": relative, "size": stat.st_size, "sha256": digest.hexdigest()}


def required_file(root: Path, relative: str) -> Path:
    path = root / relative
    if not path.exists():
        raise AttestationError(f"missing Talos build input {relative}")
    return path


def source_paths(root: Path) -> list[Path]:
    paths = [
        required_file(root, "lean-toolchain"),
        required_file(root, "lakefile.toml"),
        required_file(root, "scripts/talos_build_attestation.py"),
        required_file(root, "integration/talos/lakefile.toml"),
        required_file(root, "integration/talos/lake-manifest.json"),
        required_file(root, ".deps/talos/interpreter/lean-toolchain"),
        required_file(root, ".deps/talos/interpreter/lakefile.toml"),
        required_file(root, ".deps/talos/interpreter/lake-manifest.json"),
    ]
    for base in (
        root / "Fir",
        root / "integration" / "talos" / "FirTalos",
        root / ".deps" / "talos" / "interpreter" / "Interpreter",
    ):
        if not base.is_dir():
            raise AttestationError(f"missing Talos source directory {base}")
        paths.extend(base.rglob("*.lean"))
    paths.extend(
        required_file(root, relative)
        for relative in ("Fir.lean", "integration/talos/FirTalos.lean", ".deps/talos/interpreter/Interpreter.lean")
    )
    unique = {Path(os.path.abspath(path)) for path in paths}
    return sorted(unique, key=lambda path: path.relative_to(root).as_posix())


def output_paths(root: Path) -> list[Path]:
    base = root / "integration" / "talos" / ".lake" / "build" / "lib" / "lean" / "FirTalos"
    return [
        required_file(root, str((base / name).relative_to(root)))
        for name in (
            "Differential.olean",
            "Differential.ilean",
            "Differential.olean.hash",
            "Differential.ilean.hash",
            "Differential.trace",
        )
    ]


def command_file(root: Path, command: list[str], context: str) -> Path:
    try:
        output = subprocess.check_output(command, cwd=root, text=True).strip()
    except (OSError, subprocess.CalledProcessError) as error:
        raise AttestationError(f"cannot resolve {context}: {error}") from error
    if not output:
        raise AttestationError(f"cannot resolve {context}: empty command output")
    return Path(output).resolve()


def current_attestation(root: Path = ROOT) -> dict[str, object]:
    try:
        head = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=root, text=True
        ).strip()
    except (OSError, subprocess.CalledProcessError) as error:
        raise AttestationError(f"cannot resolve FIR HEAD: {error}") from error
    lake = shutil.which("lake")
    if lake is None:
        raise AttestationError("cannot resolve Lake executable")
    provisional: dict[str, object] = {
        "schema": SCHEMA,
        "head": head,
        "inputs": [file_record(root, path) for path in source_paths(root)],
        "tools": [
            {
                "name": "lake",
                **file_record(root, Path(lake).resolve(), "tool/lake"),
            },
            {
                "name": "lean",
                **file_record(
                    root,
                    command_file(root, ["lake", "env", "which", "lean"], "Lean executable"),
                    "tool/lean",
                ),
            },
        ],
        "outputs": [file_record(root, path) for path in output_paths(root)],
    }
    identity = hashlib.sha256(canonical_bytes(provisional)).hexdigest()
    return {**provisional, "identity": identity}


def write_attestation(path: Path, value: dict[str, object]) -> None:
    destination = Path(os.path.abspath(path))
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists() and (destination.is_symlink() or not destination.is_file()):
        raise AttestationError(f"Talos attestation is not a regular file: {destination}")
    descriptor, temporary = tempfile.mkstemp(
        prefix=".talos-build-attestation-", dir=destination.parent
    )
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(canonical_bytes(value))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, destination)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


def read_attestation(path: Path) -> dict[str, object]:
    absolute = Path(os.path.abspath(path))
    if absolute.is_symlink() or not absolute.is_file():
        raise AttestationError(f"Talos attestation is not a regular file: {absolute}")
    try:
        raw = absolute.read_bytes()
        value = json.loads(raw)
    except (OSError, json.JSONDecodeError) as error:
        raise AttestationError(f"cannot read Talos attestation {absolute}: {error}") from error
    if not isinstance(value, dict) or canonical_bytes(value) != raw:
        raise AttestationError("Talos attestation is not canonical JSON")
    return value


def verify_attestation(path: Path, root: Path = ROOT) -> dict[str, object]:
    retained = read_attestation(path)
    current = current_attestation(root)
    if retained != current:
        raise AttestationError("Talos build attestation does not match current state")
    return retained


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("record", "verify"))
    parser.add_argument("--receipt", required=True, type=Path)
    args = parser.parse_args(argv)
    if args.mode == "record":
        value = current_attestation()
        write_attestation(args.receipt, value)
        print(f"recorded exact Talos build {value['identity']} at {args.receipt}")
    else:
        value = verify_attestation(args.receipt)
        print(f"verified exact Talos build {value['identity']} at {args.receipt}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except AttestationError as error:
        print(f"Talos build attestation error: {error}", file=sys.stderr)
        raise SystemExit(2)
