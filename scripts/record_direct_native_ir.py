#!/usr/bin/env python3
"""Record and verify final-impure LCNF for direct native oracle helpers."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

from validation_harness import (
    PROTOCOL_VERSION,
    ValidationError,
    checked_sha256,
    compare_success,
    manifest_from_output as parse_corpus_manifest,
    records_from_output,
    resolve_lake_command,
    result_map,
    run,
    validate_backend_name,
)
from validation_lcnf import (
    diagnostic_name_trace,
    diagnostic_named_counts,
    named_count_items,
    positive_int_diagnostic,
    prepare_manifest as prepare_lcnf_manifest,
    required_count_observations,
    render_count_violations,
    step_trace_inventory,
    trace_name_counts,
    unsatisfied_count_requirements,
)


MANIFEST_FIELDS = {
    "version",
    "caseId",
    "entry",
    "dependencies",
    "claim",
    "requiredArtifactFragments",
    "requiredOwnershipFacts",
    "requiredOwnershipFactCounts",
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
        claim = value["claim"]
        if (
            not isinstance(claim, str)
            or not claim
            or claim != claim.strip()
            or "\n" in claim
        ):
            raise ValidationError(
                f"{case_id}: native IR claim must be a nonempty single line"
            )
        required_fragments = value["requiredArtifactFragments"]
        if (
            not isinstance(required_fragments, list)
            or any(
                not isinstance(fragment, str) or not fragment
                for fragment in required_fragments
            )
            or len(required_fragments) != len(set(required_fragments))
        ):
            raise ValidationError(
                f"{case_id}: required native IR fragments must be unique nonempty strings"
            )
        required_ownership_facts = value["requiredOwnershipFacts"]
        if (
            not isinstance(required_ownership_facts, list)
            or any(
                not isinstance(fact, str) or not fact
                for fact in required_ownership_facts
            )
            or len(required_ownership_facts)
            != len(set(required_ownership_facts))
        ):
            raise ValidationError(
                f"{case_id}: required ownership facts must be unique nonempty strings"
            )
        required_ownership_fact_counts = value["requiredOwnershipFactCounts"]
        if not isinstance(required_ownership_fact_counts, list):
            raise ValidationError(
                f"{case_id}: required ownership fact counts must be a list"
            )
        count_facts: set[str] = set()
        for requirement in required_ownership_fact_counts:
            if (
                not isinstance(requirement, dict)
                or set(requirement) != {"fact", "minimum", "maximum"}
            ):
                raise ValidationError(
                    f"{case_id}: ownership fact count requirement is malformed"
                )
            fact = requirement["fact"]
            minimum = requirement["minimum"]
            maximum = requirement["maximum"]
            if not isinstance(fact, str) or not fact or fact in count_facts:
                raise ValidationError(
                    f"{case_id}: ownership fact count names must be unique "
                    "nonempty strings"
                )
            count_facts.add(fact)
            if (
                isinstance(minimum, bool)
                or not isinstance(minimum, int)
                or minimum < 0
                or (
                    maximum is not None
                    and (
                        isinstance(maximum, bool)
                        or not isinstance(maximum, int)
                        or maximum < minimum
                    )
                )
            ):
                raise ValidationError(
                    f"{case_id}: ownership fact count bounds are invalid for {fact}"
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
                "claim": claim,
                "requiredArtifactFragments": required_fragments,
                "requiredOwnershipFacts": required_ownership_facts,
                "requiredOwnershipFactCounts": required_ownership_fact_counts,
                "expectedArtifactSha256": digest,
            }
        )
    if not descriptors:
        raise ValidationError(
            f"native IR manifest emitted no descriptors: {' '.join(command)}"
        )
    return descriptors


INC_PATTERN = re.compile(
    r"^\s*inc(?P<attributes>(?:\[[^\]]+\])*)\s+(?P<target>[^;]+);$"
)
DEC_PATTERN = re.compile(
    r"^\s*dec(?P<attributes>(?:\[[^\]]+\])*)\s+(?P<target>[^;]+);$"
)
ATTRIBUTE_PATTERN = re.compile(r"\[([^\]]+)\]")
PROJECT_PATTERN = re.compile(
    r"^\s*let\s+(?P<result>\S+)\s+:=\s+"
    r"oproj\[(?P<index>\d+)\]\s+(?P<subject>[^;]+);$"
)
IS_SHARED_PATTERN = re.compile(
    r"^\s*let\s+(?P<result>\S+)\s+:=\s+"
    r"isShared\s+(?P<subject>[^;]+);$"
)
OSET_PATTERN = re.compile(
    r"^\s*oset\s+(?P<storage>\S+)\s+\[(?P<index>\d+)\]\s+:="
)
CTOR_PATTERN = re.compile(
    r"^\s*let\s+(?P<result>\S+)\s+:=\s+"
    r"ctor_\d+\[(?P<constructor>[^\]]+)\]"
)
DECLARATION_PATTERN = re.compile(r"^def\s+(?P<name>\S+)")


def normalized_local(value: str) -> str:
    value = value.strip()
    if value.startswith("◾"):
        value = value[1:].strip()
    return re.sub(r"\.\d+$", "", value)


def constructor_suffix(name: str) -> str:
    parts = name.split(".")
    return ".".join(parts[-2:]) if len(parts) >= 2 else name


def ownership_inventory(artifact_text: str) -> dict:
    operations: list[dict] = []
    fact_counts: dict[str, int] = {}
    projections: dict[str, tuple[str, int]] = {}
    unknown_attributes: set[str] = set()

    def add_fact(fact: str) -> None:
        fact_counts[fact] = fact_counts.get(fact, 0) + 1

    for line_number, line in enumerate(artifact_text.splitlines(), start=1):
        match = DECLARATION_PATTERN.match(line)
        if match is not None:
            projections.clear()
            declaration = constructor_suffix(match["name"])
            fact = f"declaration:{declaration}"
            operations.append(
                {
                    "kind": "declaration",
                    "line": line_number,
                    "name": declaration,
                    "fact": fact,
                }
            )
            add_fact(fact)
            continue

        match = PROJECT_PATTERN.match(line)
        if match is not None:
            result = match["result"]
            subject = normalized_local(match["subject"])
            index = int(match["index"])
            projections[result] = (subject, index)
            fact = f"project:{subject}:index={index}"
            operations.append(
                {
                    "kind": "project",
                    "line": line_number,
                    "result": normalized_local(result),
                    "subject": subject,
                    "index": index,
                    "fact": fact,
                }
            )
            add_fact(fact)
            continue

        match = IS_SHARED_PATTERN.match(line)
        if match is not None:
            subject = normalized_local(match["subject"])
            fact = f"isShared:{subject}"
            operations.append(
                {
                    "kind": "isShared",
                    "line": line_number,
                    "subject": subject,
                    "fact": fact,
                }
            )
            add_fact(fact)
            continue

        match = INC_PATTERN.match(line)
        if match is not None:
            attributes = ATTRIBUTE_PATTERN.findall(match["attributes"])
            numeric = [value for value in attributes if value.isdecimal()]
            amount = int(numeric[0]) if numeric else 1
            if len(numeric) > 1:
                unknown_attributes.update(numeric[1:])
            named_attributes = {
                value for value in attributes if not value.isdecimal()
            }
            unknown_attributes.update(
                named_attributes - {"persistent", "ref"}
            )
            target = normalized_local(match["target"])
            persistent = "persistent" in named_attributes
            reference = "ref" in named_attributes
            fact = (
                f"inc:{target}:amount={amount}:persistent="
                f"{str(persistent).lower()}:reference={str(reference).lower()}"
            )
            operations.append(
                {
                    "kind": "inc",
                    "line": line_number,
                    "target": target,
                    "amount": amount,
                    "persistent": persistent,
                    "reference": reference,
                    "fact": fact,
                }
            )
            add_fact(fact)
            continue

        match = DEC_PATTERN.match(line)
        if match is not None:
            attributes = ATTRIBUTE_PATTERN.findall(match["attributes"])
            unknown_attributes.update(set(attributes) - {"ref"})
            raw_target = match["target"].strip()
            target = normalized_local(raw_target)
            reference = "ref" in attributes
            fact = f"dec:{target}:reference={str(reference).lower()}"
            operations.append(
                {
                    "kind": "dec",
                    "line": line_number,
                    "target": target,
                    "reference": reference,
                    "fact": fact,
                }
            )
            add_fact(fact)
            projection = projections.get(raw_target)
            if projection is not None:
                subject, index = projection
                project_dec_fact = f"project-dec:{subject}:index={index}"
                operations.append(
                    {
                        "kind": "project-dec",
                        "line": line_number,
                        "subject": subject,
                        "index": index,
                        "fact": project_dec_fact,
                    }
                )
                add_fact(project_dec_fact)
            continue

        match = OSET_PATTERN.match(line)
        if match is not None:
            index = int(match["index"])
            fact = f"oset:index={index}"
            operations.append(
                {
                    "kind": "oset",
                    "line": line_number,
                    "storage": normalized_local(match["storage"]),
                    "index": index,
                    "fact": fact,
                }
            )
            add_fact(fact)
            continue

        match = CTOR_PATTERN.match(line)
        if match is not None:
            constructor = constructor_suffix(match["constructor"])
            fact = f"ctor:{constructor}"
            operations.append(
                {
                    "kind": "ctor",
                    "line": line_number,
                    "result": normalized_local(match["result"]),
                    "constructor": constructor,
                    "fact": fact,
                }
            )
            add_fact(fact)

    return {
        "version": 1,
        "operations": operations,
        "facts": sorted(fact_counts),
        "factCounts": [
            {"fact": fact, "count": count}
            for fact, count in sorted(fact_counts.items())
        ],
        "unknownAttributes": sorted(unknown_attributes),
    }


def execute_backend_case(
    executable: Path,
    backend: str,
    case_id: str,
    root: Path,
) -> dict:
    command = [str(executable), "--case", case_id]
    completed = run(command, root)
    if completed.returncode != 0:
        raise ValidationError(
            f"{backend}/{case_id}: process exited {completed.returncode}:\n"
            f"{completed.stderr}"
        )
    results = result_map(records_from_output(completed.stdout, command), backend)
    if set(results) != {case_id}:
        raise ValidationError(
            f"{backend}/{case_id}: backend returned {sorted(results)}"
        )
    return results[case_id]


def direct_path_evidence(
    descriptor: dict,
    native_result: dict,
    lcnf_result: dict,
) -> tuple[dict, list[str]]:
    case_id = descriptor["id"]
    failures: list[str] = []

    observation_matches, native_observation, lcnf_observation = compare_success(
        native_result, lcnf_result
    )
    if not observation_matches:
        failures.append(
            f"{case_id}: direct native and LCNF observations differ"
        )

    expected_trace = descriptor["requiredExecutedLcnfFormTrace"]
    trace_present, observed_trace_value = diagnostic_name_trace(
        lcnf_result, "executed-lcnf-form-trace"
    )
    trace_valid = trace_present and observed_trace_value is not None
    observed_trace = observed_trace_value if trace_valid else []
    trace_matches = (
        trace_valid
        and expected_trace is not None
        and observed_trace == expected_trace
    )
    if not trace_matches:
        failures.append(
            f"{case_id}: direct LCNF executed form trace does not match its contract"
        )

    counts_present, observed_counts_value = diagnostic_named_counts(
        lcnf_result,
        "executed-lcnf-form-counts",
        "form",
    )
    counts_valid = counts_present and observed_counts_value is not None
    observed_counts = observed_counts_value if counts_valid else {}
    trace_counts = trace_name_counts(observed_trace)
    counts_match_trace = counts_valid and observed_counts == trace_counts
    if not counts_match_trace:
        failures.append(
            f"{case_id}: direct LCNF form counts disagree with its executed trace"
        )
    unsatisfied_counts = unsatisfied_count_requirements(
        descriptor["requiredExecutedLcnfFormCounts"],
        observed_counts,
        "form",
    )
    if unsatisfied_counts:
        failures.append(
            f"{case_id}: direct LCNF form counts violate their contract"
        )

    step_trace_present, step_trace_value = diagnostic_name_trace(
        lcnf_result, "executed-step-trace"
    )
    step_trace_valid = step_trace_present and step_trace_value is not None
    step_trace = step_trace_value if step_trace_valid else []
    projected_forms, administrative_counts, unknown_steps = (
        step_trace_inventory(step_trace)
    )
    step_forms_match = step_trace_valid and projected_forms == observed_trace
    if not step_forms_match:
        failures.append(
            f"{case_id}: direct LCNF step trace does not project to its form trace"
        )
    if unknown_steps:
        failures.append(
            f"{case_id}: direct LCNF step trace contains unknown transitions"
        )
    required_administrative = descriptor["requiredAdministrativeStepKinds"]
    missing_administrative = [
        kind
        for kind in required_administrative
        if administrative_counts.get(kind, 0) == 0
    ]
    if missing_administrative:
        failures.append(
            f"{case_id}: direct LCNF step trace omits required administrative transitions"
        )

    interpreter_steps_present, interpreter_steps = positive_int_diagnostic(
        lcnf_result, "interpreter-steps"
    )
    step_count_matches = (
        interpreter_steps_present
        and interpreter_steps is not None
        and interpreter_steps == len(step_trace)
    )
    if not step_count_matches:
        failures.append(
            f"{case_id}: direct LCNF interpreter-step count disagrees with its trace"
        )

    evidence = {
        "nativeBackend": native_result["backend"],
        "lcnfBackend": lcnf_result["backend"],
        "observationMatches": observation_matches,
        "nativeObservation": native_observation,
        "lcnfObservation": lcnf_observation,
        "requiredExecutedLcnfFormTrace": expected_trace,
        "executedLcnfFormTrace": observed_trace,
        "formTraceMatches": trace_matches,
        "requiredExecutedLcnfFormCounts": descriptor[
            "requiredExecutedLcnfFormCounts"
        ],
        "executedLcnfFormCounts": named_count_items(
            observed_counts, "form", "count"
        ),
        "formCountsMatchTrace": counts_match_trace,
        "unsatisfiedFormCounts": unsatisfied_counts,
        "executedStepTrace": step_trace,
        "stepFormsMatch": step_forms_match,
        "unknownStepKinds": unknown_steps,
        "requiredAdministrativeStepKinds": required_administrative,
        "executedAdministrativeStepCounts": named_count_items(
            administrative_counts, "kind", "count"
        ),
        "missingAdministrativeStepKinds": missing_administrative,
        "interpreterSteps": interpreter_steps,
        "stepCountMatches": step_count_matches,
        "matches": not failures,
        "failures": failures,
    }
    return evidence, failures


def collect_direct_path_evidence(
    descriptors: list[dict],
    selected_ids: list[str],
    native_executable: Path,
    lcnf_executable: Path,
    root: Path,
) -> dict[str, dict]:
    descriptor_by_id = {
        descriptor["id"]: descriptor for descriptor in descriptors
    }
    unknown = sorted(set(selected_ids) - set(descriptor_by_id))
    if unknown:
        raise ValidationError(
            f"native IR attestation case(s) missing from direct manifest: "
            f"{','.join(unknown)}"
        )
    evidence_by_id: dict[str, dict] = {}
    for case_id in selected_ids:
        native_result = execute_backend_case(
            native_executable, "direct-native", case_id, root
        )
        lcnf_result = execute_backend_case(
            lcnf_executable, "direct-lcnf", case_id, root
        )
        evidence, _ = direct_path_evidence(
            descriptor_by_id[case_id],
            native_result,
            lcnf_result,
        )
        evidence_by_id[case_id] = evidence
    return evidence_by_id


def attest_artifacts(
    descriptors: list[dict],
    out_dir: Path,
    selected: list[str] | None = None,
    verify_digest: bool = True,
    direct_path_evidence_by_id: dict[str, dict] | None = None,
) -> tuple[list[dict], list[str]]:
    descriptor_by_id = {item["caseId"]: item for item in descriptors}
    selected_ids = selected or sorted(descriptor_by_id)
    if len(selected_ids) != len(set(selected_ids)):
        raise ValidationError("native IR attestation cases must be unique")
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
        artifact_matches = actual_digest == expected_digest
        try:
            artifact_text = artifact.decode("utf-8")
        except UnicodeDecodeError as error:
            raise ValidationError(
                f"{case_id}: recorded native IR artifact is not UTF-8"
            ) from error
        required_fragments = descriptor["requiredArtifactFragments"]
        missing_fragments = [
            fragment
            for fragment in required_fragments
            if fragment not in artifact_text
        ]
        claim_matches = not missing_fragments
        inventory = ownership_inventory(artifact_text)
        required_ownership_facts = descriptor["requiredOwnershipFacts"]
        observed_ownership_facts = set(inventory["facts"])
        missing_ownership_facts = [
            fact
            for fact in required_ownership_facts
            if fact not in observed_ownership_facts
        ]
        observed_ownership_fact_counts = {
            item["fact"]: item["count"]
            for item in inventory["factCounts"]
        }
        required_ownership_fact_counts = descriptor[
            "requiredOwnershipFactCounts"
        ]
        ownership_fact_count_observations = required_count_observations(
            required_ownership_fact_counts,
            observed_ownership_fact_counts,
            "fact",
        )
        unsatisfied_ownership_fact_counts = unsatisfied_count_requirements(
            required_ownership_fact_counts,
            observed_ownership_fact_counts,
            "fact",
        )
        ownership_fact_counts_match = not unsatisfied_ownership_fact_counts
        ownership_matches = (
            not missing_ownership_facts
            and ownership_fact_counts_match
            and not inventory["unknownAttributes"]
        )
        matches = artifact_matches and claim_matches and ownership_matches
        direct_path = None
        if direct_path_evidence_by_id is not None:
            direct_path = direct_path_evidence_by_id.get(case_id)
            if direct_path is None:
                raise ValidationError(
                    f"{case_id}: missing direct structural path evidence"
                )
            matches = matches and direct_path["matches"]
        record = {
            "version": PROTOCOL_VERSION,
            "caseId": case_id,
            "entry": entry,
            "dependencies": descriptor["dependencies"],
            "claim": descriptor["claim"],
            "requiredArtifactFragments": required_fragments,
            "missingArtifactFragments": missing_fragments,
            "claimMatches": claim_matches,
            "requiredOwnershipFacts": required_ownership_facts,
            "missingOwnershipFacts": missing_ownership_facts,
            "requiredOwnershipFactCounts": required_ownership_fact_counts,
            "observedOwnershipFactCounts": ownership_fact_count_observations,
            "unsatisfiedOwnershipFactCounts": (
                unsatisfied_ownership_fact_counts
            ),
            "ownershipFactCountsMatch": ownership_fact_counts_match,
            "ownershipMatches": ownership_matches,
            "ownershipInventory": inventory,
            "artifact": "program.lcnf",
            "artifactBytes": len(artifact),
            "artifactSha256": actual_digest,
            "expectedArtifactSha256": expected_digest,
            "artifactMatches": artifact_matches,
            "matches": matches,
            "declarations": declarations,
            "forms": forms,
        }
        if direct_path is not None:
            record["directPath"] = direct_path
        case_dir.mkdir(parents=True, exist_ok=True)
        (case_dir / "attestation.json").write_text(
            json.dumps(record, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        records.append(record)
        if direct_path is not None and not direct_path["matches"]:
            direct_failures = direct_path.get("failures")
            if (
                not isinstance(direct_failures, list)
                or not direct_failures
                or any(
                    not isinstance(failure, str) or not failure
                    for failure in direct_failures
                )
            ):
                direct_failures = [
                    f"{case_id}: direct structural path evidence failed"
                ]
            failures.extend(direct_failures)
        if missing_fragments:
            failures.append(
                f"{case_id}: native IR no longer supports its semantic claim; "
                f"missing artifact fragments {missing_fragments!r}"
            )
        if missing_ownership_facts:
            failures.append(
                f"{case_id}: native IR ownership inventory omits required facts "
                f"{missing_ownership_facts!r}"
            )
        if unsatisfied_ownership_fact_counts:
            violations = render_count_violations(
                unsatisfied_ownership_fact_counts, "fact"
            )
            failures.append(
                f"{case_id}: native IR ownership fact counts violate their "
                f"contract: {violations}"
            )
        if inventory["unknownAttributes"]:
            failures.append(
                f"{case_id}: native IR ownership inventory has unknown attributes "
                f"{inventory['unknownAttributes']!r}"
            )
        if verify_digest and not artifact_matches:
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
        help="reuse existing Lean modules and direct executables",
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
            [
                "lake",
                "build",
                "Fir.Validation.DirectLCNF",
                "fir-direct-native",
                "fir-direct-lcnf",
            ],
            root,
        )
        if built.returncode != 0:
            sys.stderr.write(built.stdout + built.stderr)
            raise ValidationError("failed to build direct native IR recorder inputs")
    native_executable = resolve_lake_command(root, "fir-direct-native")
    lcnf_executable = resolve_lake_command(root, "fir-direct-lcnf")
    manifest_command = [str(native_executable), "--native-oracle-manifest"]
    manifest = run(manifest_command, root)
    if manifest.returncode != 0:
        raise ValidationError(
            "failed to read direct native IR manifest:\n" + manifest.stderr
        )
    descriptors = parse_manifest(manifest.stdout, manifest_command)
    descriptor_by_id = {
        descriptor["caseId"]: descriptor for descriptor in descriptors
    }
    selected_ids = args.cases or sorted(descriptor_by_id)
    if len(selected_ids) != len(set(selected_ids)):
        raise ValidationError("native IR attestation cases must be unique")
    unknown = sorted(set(selected_ids) - set(descriptor_by_id))
    if unknown:
        raise ValidationError(
            f"unknown native IR attestation case(s): {','.join(unknown)}"
        )
    corpus_manifest_command = [str(native_executable), "--manifest"]
    corpus_manifest = run(corpus_manifest_command, root)
    if corpus_manifest.returncode != 0:
        raise ValidationError(
            "failed to read direct LCNF corpus manifest:\n"
            + corpus_manifest.stderr
        )
    corpus_descriptors = prepare_lcnf_manifest(
        parse_corpus_manifest(
            corpus_manifest.stdout,
            corpus_manifest_command,
        )
    )
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
    direct_path_evidence_by_id = collect_direct_path_evidence(
        corpus_descriptors,
        selected_ids,
        native_executable,
        lcnf_executable,
        root,
    )
    records, failures = attest_artifacts(
        descriptors,
        out_dir,
        selected_ids,
        verify_digest=not args.record,
        direct_path_evidence_by_id=direct_path_evidence_by_id,
    )
    for record in records:
        status = "RECORDED" if args.record else ("PASS" if record["matches"] else "FAIL")
        print(
            f"{status} {record['caseId']} "
            f"native-ir sha256={record['artifactSha256']}"
        )
    if failures:
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
