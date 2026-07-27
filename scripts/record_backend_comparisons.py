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
    "witnesses",
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
WITNESS_FIELDS = {
    "caseId",
    "referenceResultSha256",
    "candidateResultSha256",
    "referenceObservation",
    "candidateObservation",
    "equal",
}
ORACLE_POLICY_KIND = "fir-backend-comparison-oracle-policy"
ORACLE_POLICY_FIELDS = {
    "version",
    "kind",
    "oracle",
    "requiredCandidates",
    "minimumCases",
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


def validate_witnesses(
    value: object,
    comparisons: list[dict],
    reference: str,
    candidate: str,
) -> None:
    context = f"{reference}->{candidate} comparison witnesses"
    if not isinstance(value, list) or len(value) != len(comparisons):
        raise core.ValidationError(
            f"{context} do not cover every compared case"
        )
    for witness, comparison in zip(value, comparisons, strict=True):
        if not isinstance(witness, dict) or set(witness) != WITNESS_FIELDS:
            raise core.ValidationError(f"{context} have a malformed entry")
        case_id = core.validate_backend_name(
            witness["caseId"], f"{context} case ID"
        )
        core.checked_sha256(
            witness["referenceResultSha256"],
            f"{context} {case_id} reference result",
        )
        core.checked_sha256(
            witness["candidateResultSha256"],
            f"{context} {case_id} candidate result",
        )
        reference_observation = witness["referenceObservation"]
        candidate_observation = witness["candidateObservation"]
        equal = reference_observation == candidate_observation
        if (
            case_id != comparison["caseId"]
            or not isinstance(reference_observation, dict)
            or not isinstance(candidate_observation, dict)
            or not isinstance(witness["equal"], bool)
            or witness["equal"] is not equal
            or witness["equal"] is not comparison["equal"]
        ):
            raise core.ValidationError(
                f"{context} disagree with retained comparison evidence"
            )


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
    validate_witnesses(
        value["witnesses"],
        comparison["comparisons"],
        reference,
        candidate,
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
    result_artifacts: dict[tuple[str, str], tuple[str, dict]],
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
    witnesses: list[dict] = []
    for compared in comparison["comparisons"]:
        case_id = compared["caseId"]
        try:
            reference_sha256, reference_record = result_artifacts[
                (case_id, reference)
            ]
            candidate_sha256, candidate_record = result_artifacts[
                (case_id, candidate)
            ]
        except KeyError as error:
            raise core.ValidationError(
                f"{reference}->{candidate} has no result witness for {case_id}"
            ) from error
        equal, reference_observation, candidate_observation = (
            core.compare_success(reference_record, candidate_record)
        )
        if equal is not compared["equal"]:
            raise core.ValidationError(
                f"{reference}->{candidate} result witness disagrees for "
                f"{case_id}"
            )
        witnesses.append(
            {
                "caseId": case_id,
                "referenceResultSha256": core.checked_sha256(
                    reference_sha256,
                    f"{reference}->{candidate} {case_id} reference result",
                ),
                "candidateResultSha256": core.checked_sha256(
                    candidate_sha256,
                    f"{reference}->{candidate} {case_id} candidate result",
                ),
                "referenceObservation": reference_observation,
                "candidateObservation": candidate_observation,
                "equal": equal,
            }
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
        "witnesses": witnesses,
        "matches": (
            compared_cases == len(selected_cases)
            and equal_cases == len(selected_cases)
            and finding_count == 0
        ),
    }
    record = attestation.with_record_identity(provisional)
    return verify_attestation_record(record)


def result_artifacts_from_matrix(
    path: Path,
    matrix: dict,
) -> dict[tuple[str, str], tuple[str, dict]]:
    result_artifacts: dict[tuple[str, str], tuple[str, dict]] = {}
    for artifact in matrix["artifacts"]:
        if artifact["kind"] != "backend-result":
            continue
        backend, case_id, _ = core.validation_artifact_scope(
            artifact["kind"],
            artifact["name"],
            matrix["backends"],
            matrix["selectedCases"],
        )
        if case_id is None:
            raise core.ValidationError(
                "verified backend result artifact has no case"
            )
        content = core.verify_evidence_file(
            path.parent,
            artifact["artifact"],
            artifact["sha256"],
            f"backend comparison result witness {case_id}:{backend}",
        )
        try:
            record = json.loads(content.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise core.ValidationError(
                f"backend comparison result witness is not JSON: "
                f"{case_id}:{backend}"
            ) from error
        if not isinstance(record, dict):
            raise core.ValidationError(
                f"backend comparison result witness is malformed: "
                f"{case_id}:{backend}"
            )
        recorded_case_id, _ = core.checked_record(record, backend)
        if recorded_case_id != case_id:
            raise core.ValidationError(
                f"backend comparison result witness disagrees with its name: "
                f"{case_id}:{backend}"
            )
        key = (case_id, backend)
        if key in result_artifacts:
            raise core.ValidationError(
                f"duplicate backend comparison result witness: "
                f"{case_id}:{backend}"
            )
        result_artifacts[key] = (artifact["sha256"], record)
    return result_artifacts


def records_from_matrix(path: Path) -> list[dict]:
    matrix = core.verify_matrix_artifact(path)
    result_artifacts = result_artifacts_from_matrix(path, matrix)
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
        records.append(
            record_from_verified_pair(
                matrix,
                pair,
                content,
                result_artifacts,
            )
        )
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


def validate_oracle_policy(value: object) -> dict:
    if (
        not isinstance(value, dict)
        or set(value) != ORACLE_POLICY_FIELDS
        or value["version"] != core.PROTOCOL_VERSION
        or isinstance(value["version"], bool)
        or value["kind"] != ORACLE_POLICY_KIND
    ):
        raise core.ValidationError(
            "backend comparison oracle policy has an unsupported schema"
        )
    oracle = core.validate_backend_name(
        value["oracle"], "comparison oracle"
    )
    raw_candidates = value["requiredCandidates"]
    if not isinstance(raw_candidates, list) or not raw_candidates:
        raise core.ValidationError(
            "comparison oracle policy requires candidate backends"
        )
    candidates = [
        core.validate_backend_name(
            candidate, "comparison oracle candidate"
        )
        for candidate in raw_candidates
    ]
    if (
        candidates != sorted(candidates)
        or len(candidates) != len(set(candidates))
        or oracle in candidates
    ):
        raise core.ValidationError(
            "comparison oracle candidates must be sorted, unique, and "
            "different from the oracle"
        )
    minimum_cases = value["minimumCases"]
    if (
        isinstance(minimum_cases, bool)
        or not isinstance(minimum_cases, int)
        or minimum_cases <= 0
    ):
        raise core.ValidationError(
            "comparison oracle minimumCases must be a positive integer"
        )
    return value


def read_oracle_policy(path: Path) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise core.ValidationError(
            f"cannot read backend comparison oracle policy {path}: {error}"
        ) from error
    return validate_oracle_policy(value)


def verify_oracle_policy(manifest: object, policy: object) -> dict:
    checked_manifest = verify_attestation_manifest_value(manifest)
    checked_policy = validate_oracle_policy(policy)
    oracle = checked_policy["oracle"]
    candidates = checked_policy["requiredCandidates"]
    minimum_cases = checked_policy["minimumCases"]
    record_by_id = {
        record["recordId"]: record
        for record in checked_manifest["records"]
    }
    required: list[dict] = []
    for candidate in candidates:
        record_id = f"{oracle}->{candidate}"
        record = record_by_id.get(record_id)
        if record is None:
            raise core.ValidationError(
                f"comparison oracle policy is missing required edge "
                f"{record_id}"
            )
        if not record["matches"]:
            raise core.ValidationError(
                f"comparison oracle edge does not match: {record_id}"
            )
        if len(record["selectedCases"]) < minimum_cases:
            raise core.ValidationError(
                f"comparison oracle edge {record_id} covers "
                f"{len(record['selectedCases'])} cases, fewer than "
                f"{minimum_cases}"
            )
        required.append(record)

    first = required[0]
    contract = (
        first["matrixSelectionSha256"],
        first["matrixRunSha256"],
        first["selectedCases"],
    )
    for record in required[1:]:
        if (
            record["matrixSelectionSha256"],
            record["matrixRunSha256"],
            record["selectedCases"],
        ) != contract:
            raise core.ValidationError(
                "comparison oracle edges disagree on their matrix "
                "selection, run, or ordered case set"
            )
    selected_cases = first["selectedCases"]
    for record in required:
        if (
            record["comparedCases"] != len(selected_cases)
            or record["equalCases"] != len(selected_cases)
            or record["findingCount"] != 0
            or len(record["witnesses"]) != len(selected_cases)
        ):
            raise core.ValidationError(
                f"comparison oracle edge is not complete: "
                f"{record['recordId']}"
            )
    return {
        "policySha256": core.canonical_json_sha256(checked_policy),
        "attestationContractSha256": checked_manifest["identity"]["contract"],
        "attestationEvidenceSha256": checked_manifest["identity"]["evidence"],
        "oracle": oracle,
        "requiredCandidates": candidates,
        "matrixSelectionSha256": first["matrixSelectionSha256"],
        "matrixRunSha256": first["matrixRunSha256"],
        "selectedCaseCount": len(selected_cases),
        "comparisonCount": sum(
            record["comparedCases"] for record in required
        ),
        "witnessCount": sum(len(record["witnesses"]) for record in required),
    }


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
    result.add_argument(
        "--policy",
        type=Path,
        help=(
            "offline oracle-acceptance policy relative to the repository root"
        ),
    )
    return result


def print_oracle_acceptance(summary: dict) -> None:
    candidates = ",".join(summary["requiredCandidates"])
    print(
        f"accepted {summary['oracle']} comparison oracle for "
        f"{candidates}: {summary['selectedCaseCount']} cases, "
        f"{summary['comparisonCount']} comparisons, "
        f"{summary['witnessCount']} witnesses, "
        f"policy {summary['policySha256']}"
    )


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    root = Path(__file__).resolve().parent.parent
    policy = None
    if args.policy is not None:
        policy_path = args.policy
        if not policy_path.is_absolute():
            policy_path = root / policy_path
        policy = read_oracle_policy(policy_path)
    if args.verify_attestations is not None:
        path = args.verify_attestations
        if not path.is_absolute():
            path = root / path
        manifest = verify_attestation_manifest(path)
        if policy is not None:
            print_oracle_acceptance(
                verify_oracle_policy(manifest, policy)
            )
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
    if policy is not None:
        print_oracle_acceptance(verify_oracle_policy(manifest, policy))
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
