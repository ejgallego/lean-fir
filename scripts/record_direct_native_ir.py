#!/usr/bin/env python3
"""Record and verify final-impure LCNF for direct native oracle helpers."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from validation_harness import (
    PROTOCOL_VERSION,
    ValidationError,
    checked_sha256,
    resolve_lake_command,
    run,
    validate_backend_name,
)


MANIFEST_FIELDS = {
    "version",
    "caseId",
    "entry",
    "dependencies",
    "expectedArtifactSha256",
}
ARTIFACT_FILES = (
    "program.lcnf",
    "declarations.txt",
    "forms.txt",
    "entry.txt",
)


def sha256_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def parse_manifest(output: str, command: list[str]) -> list[dict]:
    descriptors: list[dict] = []
    seen: set[str] = set()
    for line_number, line in enumerate(output.splitlines(), start=1):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValidationError(
                "native IR manifest emitted malformed JSONL "
                f"at line {line_number} from {' '.join(command)}"
            ) from error
        if not isinstance(value, dict) or not MANIFEST_FIELDS <= value.keys():
            missing = (
                sorted(MANIFEST_FIELDS - value.keys())
                if isinstance(value, dict)
                else []
            )
            detail = f": missing {','.join(missing)}" if missing else ""
            raise ValidationError(
                f"native IR manifest line {line_number} is malformed{detail}"
            )
        if value["version"] != PROTOCOL_VERSION:
            raise ValidationError(
                "native IR manifest protocol version "
                f"{value['version']} is not {PROTOCOL_VERSION}"
            )
        case_id = validate_backend_name(
            value["caseId"], f"native IR manifest line {line_number} case ID"
        )
        if case_id in seen:
            raise ValidationError(f"duplicate native IR attestation case: {case_id}")
        seen.add(case_id)
        entry = value["entry"]
        if not isinstance(entry, str) or not entry:
            raise ValidationError(f"{case_id}: native IR entry must be a nonempty string")
        dependencies = value["dependencies"]
        if (
            not isinstance(dependencies, list)
            or any(not isinstance(name, str) or not name for name in dependencies)
            or len(dependencies) != len(set(dependencies))
        ):
            raise ValidationError(
                f"{case_id}: native IR dependencies must be unique nonempty strings"
            )
        digest = checked_sha256(
            value["expectedArtifactSha256"],
            f"{case_id} expected native IR artifact",
        )
        descriptors.append(
            {
                "version": PROTOCOL_VERSION,
                "caseId": case_id,
                "entry": entry,
                "dependencies": dependencies,
                "expectedArtifactSha256": digest,
            }
        )
    if not descriptors:
        raise ValidationError(
            f"native IR manifest emitted no descriptors: {' '.join(command)}"
        )
    return descriptors


def attest_artifacts(
    descriptors: list[dict],
    out_dir: Path,
    selected: list[str] | None = None,
) -> tuple[list[dict], list[str]]:
    descriptor_by_id = {item["caseId"]: item for item in descriptors}
    selected_ids = selected or sorted(descriptor_by_id)
    unknown = sorted(set(selected_ids) - set(descriptor_by_id))
    if unknown:
        raise ValidationError(
            f"unknown native IR attestation case(s): {','.join(unknown)}"
        )
    records: list[dict] = []
    failures: list[str] = []
    for case_id in selected_ids:
        descriptor = descriptor_by_id[case_id]
        case_dir = out_dir / case_id
        contents: dict[str, bytes] = {}
        for name in ARTIFACT_FILES:
            path = case_dir / name
            try:
                contents[name] = path.read_bytes()
            except OSError as error:
                raise ValidationError(
                    f"{case_id}: missing recorded native IR artifact {name}"
                ) from error
        entry = contents["entry.txt"].decode("utf-8").strip()
        if entry != descriptor["entry"]:
            raise ValidationError(
                f"{case_id}: recorded entry {entry!r} is not {descriptor['entry']!r}"
            )
        declarations = [
            line
            for line in contents["declarations.txt"].decode("utf-8").splitlines()
            if line
        ]
        required_declarations = [entry, *descriptor["dependencies"]]
        missing_declarations = [
            name for name in required_declarations if name not in declarations
        ]
        if missing_declarations:
            raise ValidationError(
                f"{case_id}: recorded artifact omits rooted declarations "
                f"{','.join(missing_declarations)}"
            )
        forms = [
            line
            for line in contents["forms.txt"].decode("utf-8").splitlines()
            if line
        ]
        if not forms:
            raise ValidationError(f"{case_id}: recorded artifact has no LCNF forms")
        artifact = contents["program.lcnf"]
        actual_digest = sha256_bytes(artifact)
        expected_digest = descriptor["expectedArtifactSha256"]
        matches = actual_digest == expected_digest
        record = {
            "version": PROTOCOL_VERSION,
            "caseId": case_id,
            "entry": entry,
            "dependencies": descriptor["dependencies"],
            "artifact": "program.lcnf",
            "artifactBytes": len(artifact),
            "artifactSha256": actual_digest,
            "expectedArtifactSha256": expected_digest,
            "matches": matches,
            "declarations": declarations,
            "forms": forms,
        }
        case_dir.mkdir(parents=True, exist_ok=True)
        (case_dir / "attestation.json").write_text(
            json.dumps(record, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        records.append(record)
        if not matches:
            failures.append(
                f"{case_id}: native IR SHA-256 {actual_digest} "
                f"does not match {expected_digest}"
            )
    (out_dir / "attestations.json").write_text(
        json.dumps(records, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return records, failures


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument(
        "--out-dir",
        type=Path,
        default=Path("_build/validation-direct-native-ir"),
        help="artifact directory relative to the repository root",
    )
    result.add_argument(
        "--case",
        action="append",
        dest="cases",
        help="attest only this case (repeatable)",
    )
    result.add_argument(
        "--no-build",
        action="store_true",
        help="reuse existing Lean modules and direct-native executable",
    )
    result.add_argument(
        "--record",
        action="store_true",
        help="record and print actual digests without failing on mismatches",
    )
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    root = Path(__file__).resolve().parent.parent
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = root / out_dir
    if not args.no_build:
        built = run(
            ["lake", "build", "Fir.Validation.DirectLCNF", "fir-direct-native"],
            root,
        )
        if built.returncode != 0:
            sys.stderr.write(built.stdout + built.stderr)
            raise ValidationError("failed to build direct native IR recorder inputs")
    executable = resolve_lake_command(root, "fir-direct-native")
    manifest_command = [str(executable), "--native-oracle-manifest"]
    manifest = run(manifest_command, root)
    if manifest.returncode != 0:
        raise ValidationError(
            "failed to read direct native IR manifest:\n" + manifest.stderr
        )
    descriptors = parse_manifest(manifest.stdout, manifest_command)
    lean = resolve_lake_command(root, "lean")
    lean_path = run(["lake", "env", "printenv", "LEAN_PATH"], root)
    if lean_path.returncode != 0 or not lean_path.stdout.strip():
        raise ValidationError("failed to resolve direct native IR LEAN_PATH")
    runner = root / "scripts" / "validation_direct_native_ir.lean"
    recorded = run(
        [str(lean), str(runner)],
        root,
        extra_env={
            "LEAN_PATH": lean_path.stdout.strip(),
            "FIR_DIRECT_NATIVE_IR_OUT_DIR": str(out_dir),
        },
    )
    if recorded.returncode != 0:
        sys.stderr.write(recorded.stdout + recorded.stderr)
        raise ValidationError("failed to record direct native final-impure LCNF")
    records, failures = attest_artifacts(descriptors, out_dir, args.cases)
    for record in records:
        status = "RECORDED" if args.record else ("PASS" if record["matches"] else "FAIL")
        print(
            f"{status} {record['caseId']} "
            f"native-ir sha256={record['artifactSha256']}"
        )
    if failures and not args.record:
        for failure in failures:
            print(failure, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
