#!/usr/bin/env python3
"""Attest directed backend comparisons from an already-verified matrix."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import validation_attestation as attestation
import validation_harness as core


ATTESTATION_KIND = "fir-backend-comparison-attestations"
ATTESTATION_CONTRACT_KIND = "fir-backend-comparison-contract"
ATTESTATION_CONTRACT_FIELDS = (
    "recordId",
    "reference",
    "candidate",
    "matrixSelectionSha256",
    "matrixRunSha256",
    "selectedCases",
)
ATTESTATION_SPEC = attestation.EnvelopeSpec(
    kind=ATTESTATION_KIND,
    contract_kind=ATTESTATION_CONTRACT_KIND,
    contract_fields=ATTESTATION_CONTRACT_FIELDS,
    record_id_field="recordId",
)
ATTESTATION_RECORD_FIELDS = {
    "version",
    "identity",
    *ATTESTATION_CONTRACT_FIELDS,
    "comparisonArtifact",
    "comparisonArtifactBytes",
    "comparisonArtifactSha256",
    "comparedCases",
    "equalCases",
    "findingCount",
    "matches",
}
PAIR_FIELDS = {
    "reference",
    "candidate",
    "artifact",
    "sha256",
    "comparedCases",
    "equalCases",
    "findingCount",
}
COMPARISON_FIELDS = {
    "version",
    "reference",
    "candidate",
    "comparisons",
    "findings",
    "summary",
}
COMPARISON_ENTRY_FIELDS = {
    "caseId",
    "reference",
    "candidate",
    "equal",
    "case",
}
COMPARISON_SUMMARY_FIELDS = {
    "selectedCases",
    "comparedCases",
    "equalCases",
    "findingCount",
}


def checked_count(value: object, context: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise core.ValidationError(f"{context} must be a nonnegative integer")
    return value


def checked_selected_cases(value: object, context: str) -> list[str]:
    if not isinstance(value, list) or not value:
        raise core.ValidationError(f"{context} must be a nonempty list")
    cases = [
        core.validate_backend_name(case_id, f"{context} case ID")
        for case_id in value
    ]
    if len(cases) != len(set(cases)):
        raise core.ValidationError(f"{context} repeats a case ID")
    return cases


def validate_comparison_report(
    value: object,
    reference: str,
    candidate: str,
    selected_cases: list[str],
) -> tuple[int, int, int]:
    context = f"{reference}->{candidate} comparison"
    if (
        not isinstance(value, dict)
        or set(value) != COMPARISON_FIELDS
        or value["version"] != core.PROTOCOL_VERSION
        or isinstance(value["version"], bool)
        or value["reference"] != reference
        or value["candidate"] != candidate
        or not isinstance(value["comparisons"], list)
        or not isinstance(value["findings"], list)
    ):
        raise core.ValidationError(f"{context} has an unsupported schema")

    compared_case_ids: list[str] = []
    equal_cases = 0
    for item in value["comparisons"]:
        if not isinstance(item, dict) or set(item) != COMPARISON_ENTRY_FIELDS:
            raise core.ValidationError(f"{context} has a malformed entry")
        case_id = core.validate_backend_name(
            item["caseId"], f"{context} case ID"
        )
        case = item["case"]
        if (
            item["reference"] != reference
            or item["candidate"] != candidate
            or not isinstance(item["equal"], bool)
            or not isinstance(case, dict)
            or case.get("version") != core.PROTOCOL_VERSION
            or isinstance(case.get("version"), bool)
            or case.get("id") != case_id
        ):
            raise core.ValidationError(
                f"{context} entry disagrees with its edge or case"
            )
        compared_case_ids.append(case_id)
        equal_cases += int(item["equal"])

    compared_set = set(compared_case_ids)
    if (
        len(compared_case_ids) != len(compared_set)
        or compared_case_ids
        != [case_id for case_id in selected_cases if case_id in compared_set]
    ):
        raise core.ValidationError(
            f"{context} case IDs are duplicated, unknown, or out of order"
        )

    for finding in value["findings"]:
        if (
            not isinstance(finding, dict)
            or not {"phase", "message"} <= set(finding)
            or set(finding) - {"phase", "message", "backend", "caseId"}
            or not all(isinstance(item, str) for item in finding.values())
        ):
            raise core.ValidationError(f"{context} has a malformed finding")

    summary = value["summary"]
    if (
        not isinstance(summary, dict)
        or set(summary) != COMPARISON_SUMMARY_FIELDS
    ):
        raise core.ValidationError(f"{context} has a malformed summary")
    checked_summary = {
        field: checked_count(summary[field], f"{context} summary {field}")
        for field in COMPARISON_SUMMARY_FIELDS
    }
    compared_cases = len(compared_case_ids)
    finding_count = len(value["findings"])
    expected_summary = {
        "selectedCases": len(selected_cases),
        "comparedCases": compared_cases,
        "equalCases": equal_cases,
        "findingCount": finding_count,
    }
    if checked_summary != expected_summary:
        raise core.ValidationError(
            f"{context} summary disagrees with its evidence"
        )
    return compared_cases, equal_cases, finding_count


def verify_attestation_record(value: object) -> dict:
    if (
        not isinstance(value, dict)
        or set(value) != ATTESTATION_RECORD_FIELDS
        or value["version"] != core.PROTOCOL_VERSION
        or isinstance(value["version"], bool)
    ):
        raise core.ValidationError(
            "backend comparison attestation has an unsupported schema"
        )
    attestation.verify_record_identity(
        value, "backend comparison attestation"
    )
    reference = core.validate_backend_name(
        value["reference"], "comparison reference"
    )
    candidate = core.validate_backend_name(
        value["candidate"], "comparison candidate"
    )
    record_id = value["recordId"]
    if reference == candidate or record_id != f"{reference}->{candidate}":
        raise core.ValidationError(
            "backend comparison attestation has a malformed edge"
        )
    selection_sha256 = core.checked_sha256(
        value["matrixSelectionSha256"],
        f"{record_id} matrix selection",
    )
    run_sha256 = core.checked_sha256(
        value["matrixRunSha256"],
        f"{record_id} matrix run",
    )
    selected_cases = checked_selected_cases(
        value["selectedCases"], f"{record_id} selected cases"
    )
    artifact_sha256 = core.checked_sha256(
        value["comparisonArtifactSha256"],
        f"{record_id} comparison artifact",
    )
    artifact = value["comparisonArtifact"]
    artifact_bytes = checked_count(
        value["comparisonArtifactBytes"],
        f"{record_id} comparison artifact bytes",
    )
    if not isinstance(artifact, str) or not artifact:
        raise core.ValidationError(
            f"{record_id} comparison artifact must be nonempty UTF-8"
        )
    encoded_artifact = artifact.encode("utf-8")
    if (
        artifact_bytes != len(encoded_artifact)
        or artifact_sha256 != core.sha256_bytes(encoded_artifact)
    ):
        raise core.ValidationError(
            f"{record_id} comparison artifact derivatives disagree"
        )
    try:
        comparison = json.loads(artifact)
    except json.JSONDecodeError as error:
        raise core.ValidationError(
            f"{record_id} comparison artifact is not JSON"
        ) from error
    compared_cases, equal_cases, finding_count = validate_comparison_report(
        comparison,
        reference,
        candidate,
        selected_cases,
    )
    expected_matches = (
        compared_cases == len(selected_cases)
        and equal_cases == len(selected_cases)
        and finding_count == 0
    )
    if (
        checked_count(
            value["comparedCases"], f"{record_id} compared cases"
        )
        != compared_cases
        or checked_count(value["equalCases"], f"{record_id} equal cases")
        != equal_cases
        or checked_count(
            value["findingCount"], f"{record_id} finding count"
        )
        != finding_count
        or not isinstance(value["matches"], bool)
        or value["matches"] is not expected_matches
    ):
        raise core.ValidationError(
            f"{record_id} comparison derivatives disagree"
        )
    return value


def record_from_verified_pair(
    matrix: dict,
    pair: dict,
    comparison_content: bytes,
) -> dict:
    if not isinstance(pair, dict) or set(pair) != PAIR_FIELDS:
        raise core.ValidationError("verified matrix has a malformed pair")
    identity = matrix.get("identity")
    if (
        not isinstance(identity, dict)
        or set(identity) != {"algorithm", "selection", "run"}
        or identity["algorithm"] != "sha256"
    ):
        raise core.ValidationError("verified matrix identity is malformed")
    selected_cases = checked_selected_cases(
        matrix.get("selectedCases"), "verified matrix selected cases"
    )
    reference = core.validate_backend_name(
        pair["reference"], "verified pair reference"
    )
    candidate = core.validate_backend_name(
        pair["candidate"], "verified pair candidate"
    )
    if reference == candidate:
        raise core.ValidationError("verified pair compares a backend with itself")
    selection_sha256 = core.checked_sha256(
        identity["selection"], "verified matrix selection"
    )
    run_sha256 = core.checked_sha256(
        identity["run"], "verified matrix run"
    )
    artifact_sha256 = core.checked_sha256(
        pair["sha256"], f"{reference}->{candidate} comparison artifact"
    )
    if core.sha256_bytes(comparison_content) != artifact_sha256:
        raise core.ValidationError(
            f"{reference}->{candidate} comparison artifact SHA-256 mismatch"
        )
    try:
        artifact = comparison_content.decode("utf-8")
        comparison = json.loads(artifact)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise core.ValidationError(
            f"{reference}->{candidate} comparison artifact is not UTF-8 JSON"
        ) from error
    compared_cases, equal_cases, finding_count = validate_comparison_report(
        comparison,
        reference,
        candidate,
        selected_cases,
    )
    pair_counts = (
        checked_count(pair["comparedCases"], "verified pair compared cases"),
        checked_count(pair["equalCases"], "verified pair equal cases"),
        checked_count(pair["findingCount"], "verified pair finding count"),
    )
    if pair_counts != (compared_cases, equal_cases, finding_count):
        raise core.ValidationError(
            f"{reference}->{candidate} matrix pair disagrees with its artifact"
        )
    provisional = {
        "version": core.PROTOCOL_VERSION,
        "recordId": f"{reference}->{candidate}",
        "reference": reference,
        "candidate": candidate,
        "matrixSelectionSha256": selection_sha256,
        "matrixRunSha256": run_sha256,
        "selectedCases": selected_cases,
        "comparisonArtifact": artifact,
        "comparisonArtifactBytes": len(comparison_content),
        "comparisonArtifactSha256": artifact_sha256,
        "comparedCases": compared_cases,
        "equalCases": equal_cases,
        "findingCount": finding_count,
        "matches": (
            compared_cases == len(selected_cases)
            and equal_cases == len(selected_cases)
            and finding_count == 0
        ),
    }
    record = attestation.with_record_identity(provisional)
    return verify_attestation_record(record)


def records_from_matrix(path: Path) -> list[dict]:
    matrix = core.verify_matrix_artifact(path)
    records: list[dict] = []
    for pair in matrix["pairs"]:
        reference = pair["reference"]
        candidate = pair["candidate"]
        content = core.verify_evidence_file(
            path.parent,
            pair["artifact"],
            pair["sha256"],
            f"backend comparison attestation {reference}->{candidate}",
        )
        records.append(record_from_verified_pair(matrix, pair, content))
    return records


def build_attestation_manifest(records: list[dict]) -> dict:
    return attestation.build_envelope(
        ATTESTATION_SPEC,
        records,
        verify_attestation_record,
    )


def verify_attestation_manifest_value(value: object) -> dict:
    return attestation.verify_envelope_value(
        value,
        ATTESTATION_SPEC,
        verify_attestation_record,
    )


def verify_attestation_manifest(path: Path) -> dict:
    return attestation.read_envelope(
        path,
        ATTESTATION_SPEC,
        verify_attestation_record,
    )


def attest_matrix(path: Path, out_dir: Path) -> dict:
    manifest = build_attestation_manifest(records_from_matrix(path))
    attestation.write_retained_envelope(
        out_dir,
        "attestations.json",
        manifest,
        ATTESTATION_SPEC,
        verify_attestation_record,
    )
    return manifest


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    source = result.add_mutually_exclusive_group()
    source.add_argument(
        "--matrix",
        type=Path,
        help=(
            "already-produced matrix to verify and attest; defaults to "
            "_build/validation-v8/matrix.json"
        ),
    )
    source.add_argument(
        "--verify-attestations",
        type=Path,
        help="verify a retained bundle without reading its source matrix",
    )
    result.add_argument(
        "--out-dir",
        type=Path,
        default=Path("_build/validation-comparison-attestations"),
        help="artifact directory relative to the repository root",
    )
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    root = Path(__file__).resolve().parent.parent
    if args.verify_attestations is not None:
        path = args.verify_attestations
        if not path.is_absolute():
            path = root / path
        manifest = verify_attestation_manifest(path)
        matches = sum(int(record["matches"]) for record in manifest["records"])
        print(
            "verified backend comparison attestations "
            f"{manifest['identity']['evidence']}: "
            f"contract {manifest['identity']['contract']}, "
            f"matching edges {matches}/{len(manifest['records'])}"
        )
        return 0

    matrix_path = args.matrix or Path("_build/validation-v8/matrix.json")
    if not matrix_path.is_absolute():
        matrix_path = root / matrix_path
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = root / out_dir
    manifest = attest_matrix(matrix_path, out_dir)
    failures = 0
    for record in manifest["records"]:
        status = "PASS" if record["matches"] else "FAIL"
        failures += int(not record["matches"])
        print(
            f"{status} {record['recordId']} "
            f"{record['equalCases']}/{len(record['selectedCases'])} equal, "
            f"{record['findingCount']} findings"
        )
    print(
        "backend comparison attestation evidence "
        f"{manifest['identity']['evidence']}: "
        f"contract {manifest['identity']['contract']}"
    )
    return int(failures > 0)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except core.ValidationError as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(2)
