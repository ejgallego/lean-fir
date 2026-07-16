#!/usr/bin/env python3
"""Compare Lean's native oracle with protocol-compatible candidate backends."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Protocol


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "_build" / "validation"
PROTOCOL_VERSION = 1
MANIFEST_FIELDS = {
    "version",
    "id",
    "entry",
    "dependencies",
    "args",
    "argSchemas",
    "resultSchema",
    "tags",
    "fuel",
    "provenance",
    "requiredLcnfForms",
    "requiredExecutedLcnfForms",
    "requiredExternals",
    "requiredExecutedExternals",
    "effectProjections",
}
EFFECT_PROJECTION_FIELDS = {"external", "operation", "argSchemas", "resultSchema"}


class ValidationError(RuntimeError):
    pass


def run(
    command: list[str],
    timeout: int = 120,
    extra_env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    environment = None
    if extra_env is not None:
        environment = os.environ.copy()
        environment.update(extra_env)
    try:
        return subprocess.run(
            command,
            cwd=ROOT,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise ValidationError(f"command timed out: {' '.join(command)}") from error


def records_from_output(output: str, command: list[str]) -> list[dict]:
    records: list[dict] = []
    for line in output.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValidationError(
                f"backend emitted malformed JSONL from {' '.join(command)}: {line}"
            ) from error
        if not isinstance(value, dict) or not {
            "version",
            "caseId",
            "backend",
            "outcome",
        } <= value.keys():
            raise ValidationError(
                f"backend emitted a non-protocol JSON object from {' '.join(command)}"
            )
        records.append(value)
    if not records:
        raise ValidationError(f"backend emitted no protocol records: {' '.join(command)}")
    return records


def manifest_from_output(output: str, command: list[str]) -> list[dict]:
    """Parse and canonicalize case descriptors emitted by the native oracle."""
    descriptors: list[dict] = []
    for line_number, line in enumerate(output.splitlines(), start=1):
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise ValidationError(
                "native oracle emitted malformed manifest JSONL "
                f"at line {line_number} from {' '.join(command)}: {line}"
            ) from error
        if not isinstance(value, dict) or not MANIFEST_FIELDS <= value.keys():
            missing = sorted(MANIFEST_FIELDS - value.keys()) if isinstance(value, dict) else []
            detail = f"; missing {', '.join(missing)}" if missing else ""
            raise ValidationError(
                "native oracle emitted a non-manifest JSON object "
                f"at line {line_number} from {' '.join(command)}{detail}"
            )

        case_id = value["id"]
        entry = value["entry"]
        version = value["version"]
        dependencies = value["dependencies"]
        args = value["args"]
        arg_schemas = value["argSchemas"]
        result_schema = value["resultSchema"]
        tags = value["tags"]
        fuel = value["fuel"]
        provenance = value["provenance"]
        required_forms = value["requiredLcnfForms"]
        required_executed_forms = value["requiredExecutedLcnfForms"]
        required_externals = value["requiredExternals"]
        required_executed_externals = value["requiredExecutedExternals"]
        effect_projections = value["effectProjections"]
        if version != PROTOCOL_VERSION:
            raise ValidationError(
                f"native corpus manifest/{case_id}: protocol version {version} "
                f"is not {PROTOCOL_VERSION}"
            )
        if not isinstance(case_id, str) or not case_id:
            raise ValidationError(f"native corpus manifest line {line_number}: missing id")
        if not isinstance(entry, str) or not entry:
            raise ValidationError(f"native corpus manifest/{case_id}: missing entry")
        if not isinstance(dependencies, list) or not all(
            isinstance(dependency, str) and dependency for dependency in dependencies
        ):
            raise ValidationError(f"native corpus manifest/{case_id}: malformed dependencies")
        if len(set(dependencies)) != len(dependencies):
            raise ValidationError(f"native corpus manifest/{case_id}: duplicate dependencies")
        if not isinstance(args, list) or not isinstance(arg_schemas, list):
            raise ValidationError(f"native corpus manifest/{case_id}: malformed arguments")
        if len(args) != len(arg_schemas):
            raise ValidationError(f"native corpus manifest/{case_id}: argument arity mismatch")
        if result_schema is None:
            raise ValidationError(f"native corpus manifest/{case_id}: missing resultSchema")
        if not isinstance(tags, list) or not all(isinstance(tag, str) and tag for tag in tags):
            raise ValidationError(f"native corpus manifest/{case_id}: malformed tags")
        if len(set(tags)) != len(tags):
            raise ValidationError(f"native corpus manifest/{case_id}: duplicate tags")
        if not isinstance(fuel, int) or isinstance(fuel, bool) or fuel <= 0:
            raise ValidationError(f"native corpus manifest/{case_id}: malformed fuel")
        if not isinstance(provenance, dict) or not all(
            isinstance(provenance.get(field), str)
            for field in ("suite", "path", "revision", "note")
        ):
            raise ValidationError(f"native corpus manifest/{case_id}: missing provenance")
        if not isinstance(required_forms, list) or not all(
            isinstance(form, str) and form for form in required_forms
        ):
            raise ValidationError(
                f"native corpus manifest/{case_id}: malformed requiredLcnfForms"
            )
        if len(set(required_forms)) != len(required_forms):
            raise ValidationError(
                f"native corpus manifest/{case_id}: duplicate requiredLcnfForms"
            )
        if not isinstance(required_executed_forms, list) or not all(
            isinstance(form, str) and form for form in required_executed_forms
        ):
            raise ValidationError(
                f"native corpus manifest/{case_id}: malformed requiredExecutedLcnfForms"
            )
        if len(set(required_executed_forms)) != len(required_executed_forms):
            raise ValidationError(
                f"native corpus manifest/{case_id}: duplicate requiredExecutedLcnfForms"
            )
        if not isinstance(required_externals, list) or not all(
            isinstance(name, str) and name for name in required_externals
        ):
            raise ValidationError(
                f"native corpus manifest/{case_id}: malformed requiredExternals"
            )
        if len(set(required_externals)) != len(required_externals):
            raise ValidationError(
                f"native corpus manifest/{case_id}: duplicate requiredExternals"
            )
        if not isinstance(required_executed_externals, list) or not all(
            isinstance(name, str) and name for name in required_executed_externals
        ):
            raise ValidationError(
                f"native corpus manifest/{case_id}: malformed requiredExecutedExternals"
            )
        if len(set(required_executed_externals)) != len(required_executed_externals):
            raise ValidationError(
                f"native corpus manifest/{case_id}: duplicate requiredExecutedExternals"
            )
        if not isinstance(effect_projections, list):
            raise ValidationError(
                f"native corpus manifest/{case_id}: malformed effectProjections"
            )
        effect_externals: list[str] = []
        for projection in effect_projections:
            if not isinstance(projection, dict) or not EFFECT_PROJECTION_FIELDS <= projection.keys():
                raise ValidationError(
                    f"native corpus manifest/{case_id}: malformed effectProjections"
                )
            external = projection["external"]
            operation = projection["operation"]
            projection_arg_schemas = projection["argSchemas"]
            if (
                not isinstance(external, str)
                or not external
                or not isinstance(operation, str)
                or not operation
                or not isinstance(projection_arg_schemas, list)
            ):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: malformed effectProjections"
                )
            effect_externals.append(external)
        if len(set(effect_externals)) != len(effect_externals):
            raise ValidationError(
                f"native corpus manifest/{case_id}: duplicate effectProjections"
            )
        if not set(effect_externals) <= (
            set(required_externals) & set(required_executed_externals)
        ):
            raise ValidationError(
                f"native corpus manifest/{case_id}: effect projection externals "
                "must be required and executed"
            )

        descriptor = dict(value)
        descriptor["tags"] = sorted(tags)
        descriptor["requiredLcnfForms"] = sorted(required_forms)
        descriptor["requiredExecutedLcnfForms"] = sorted(required_executed_forms)
        descriptor["requiredExternals"] = sorted(required_externals)
        descriptor["requiredExecutedExternals"] = sorted(required_executed_externals)
        descriptor["effectProjections"] = sorted(
            (dict(projection) for projection in effect_projections),
            key=lambda projection: (projection["external"], projection["operation"]),
        )
        descriptors.append(descriptor)

    if not descriptors:
        raise ValidationError(
            f"native oracle emitted no corpus descriptors: {' '.join(command)}"
        )
    descriptors.sort(key=lambda descriptor: descriptor["id"])
    case_ids = [descriptor["id"] for descriptor in descriptors]
    duplicates = sorted({case_id for case_id in case_ids if case_ids.count(case_id) > 1})
    if duplicates:
        raise ValidationError(
            f"native corpus manifest contains duplicate case IDs: {', '.join(duplicates)}"
        )
    return descriptors


def select_cases(
    descriptors: list[dict], requested: list[str] | None, tag: str | None
) -> list[str]:
    all_cases = [descriptor["id"] for descriptor in descriptors]
    known = set(all_cases)
    if requested:
        duplicates = sorted({case_id for case_id in requested if requested.count(case_id) > 1})
        if duplicates:
            raise ValidationError(
                f"validation case selected more than once: {', '.join(duplicates)}"
            )
        unknown = sorted(set(requested) - known)
        if unknown:
            raise ValidationError(f"unknown validation case(s): {', '.join(unknown)}")
        return requested
    if tag:
        selected = [descriptor["id"] for descriptor in descriptors if tag in descriptor["tags"]]
        if not selected:
            raise ValidationError(f"corpus tag selected no cases: {tag}")
        return selected
    return all_cases


def write_corpus_manifest(out_dir: Path, descriptors: list[dict]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "corpus.json").write_text(
        json.dumps(
            {"version": PROTOCOL_VERSION, "cases": descriptors},
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


def checked_record(record: dict, backend: str) -> tuple[str, dict]:
    if record.get("version") != PROTOCOL_VERSION:
        raise ValidationError(
            f"{backend}: protocol version {record.get('version')} is not {PROTOCOL_VERSION}"
        )
    if record.get("backend") != backend:
        raise ValidationError(f"expected backend {backend}, got {record.get('backend')}")
    case_id = record.get("caseId")
    if not isinstance(case_id, str) or not case_id:
        raise ValidationError(f"{backend}: missing caseId")
    outcome = record.get("outcome")
    if not isinstance(outcome, dict) or len(outcome) != 1:
        raise ValidationError(f"{backend}/{case_id}: malformed outcome")
    return case_id, outcome


def result_map(records: list[dict], backend: str) -> dict[str, dict]:
    results: dict[str, dict] = {}
    for record in records:
        case_id, _ = checked_record(record, backend)
        if case_id in results:
            raise ValidationError(f"{backend}: duplicate result for {case_id}")
        results[case_id] = record
    return results


def diagnostics(record: dict) -> dict[str, str]:
    result: dict[str, str] = {}
    items = record.get("diagnostics", [])
    if not isinstance(items, list):
        raise ValidationError(
            f"{record.get('backend', 'backend')}/{record.get('caseId', '?')}: "
            "malformed diagnostics"
        )
    for item in items:
        if (
            not isinstance(item, dict)
            or not isinstance(item.get("key"), str)
            or not item["key"]
            or not isinstance(item.get("value"), str)
        ):
            raise ValidationError(
                f"{record.get('backend', 'backend')}/{record.get('caseId', '?')}: "
                "malformed diagnostic"
            )
        if item["key"] in result:
            raise ValidationError(
                f"{record.get('backend', 'backend')}/{record.get('caseId', '?')}: "
                f"duplicate diagnostic {item['key']}"
            )
        result[item["key"]] = item["value"]
    return result


def diagnostic_forms(record: dict | None, key: str) -> tuple[bool, list[str]]:
    """Return whether a comma-separated form diagnostic exists and its canonical set."""
    if record is None:
        return False, []
    values = diagnostics(record)
    if key not in values:
        return False, []
    forms = [form.strip() for form in values[key].split(",") if form.strip()]
    return True, sorted(set(forms))


def positive_int_diagnostic(record: dict | None, key: str) -> tuple[bool, int | None]:
    """Return a positive decimal diagnostic, preserving absence vs invalidity."""
    if record is None:
        return False, None
    values = diagnostics(record)
    if key not in values:
        return False, None
    raw_value = values[key]
    if not raw_value.isdecimal():
        return True, None
    value = int(raw_value)
    return True, value if value > 0 else None


def coverage_report(
    descriptors: list[dict], results: dict[str, dict], selected: list[str]
) -> tuple[dict, list[str]]:
    """Build deterministic static and executed LCNF and external coverage.

    `lcnf-forms` describes the forms in the compiled artifact;
    `executed-lcnf-forms` describes the forms reached by the interpreter.
    `externals` and `executed-externals` make the analogous distinction for
    runtime primitives.  The backend's `missing-*` diagnostics are checked
    against the independently computed missing sets.  Execution telemetry is
    required for every result, while path obligations are active only when
    the corresponding executed requirement list is nonempty.
    """
    descriptor_by_id = {descriptor["id"]: descriptor for descriptor in descriptors}
    cases: list[dict] = []
    failures: list[str] = []
    static_required: set[str] = set()
    static_observed: set[str] = set()
    executed_required: set[str] = set()
    executed_observed: set[str] = set()
    static_missing_count = 0
    executed_missing_count = 0
    executed_diagnostic_count = 0
    executed_requirement_count = 0
    static_external_required: set[str] = set()
    static_external_observed: set[str] = set()
    executed_external_required: set[str] = set()
    executed_external_observed: set[str] = set()
    static_external_missing_count = 0
    executed_external_missing_count = 0
    static_external_diagnostic_count = 0
    executed_external_diagnostic_count = 0
    static_external_missing_diagnostic_count = 0
    executed_external_missing_diagnostic_count = 0
    static_external_requirement_count = 0
    executed_external_requirement_count = 0
    interpreter_steps: list[int] = []

    for case_id in sorted(selected):
        descriptor = descriptor_by_id[case_id]
        record = results.get(case_id)
        static_present, observed_static = diagnostic_forms(record, "lcnf-forms")
        executed_present, observed_executed = diagnostic_forms(
            record, "executed-lcnf-forms"
        )
        steps_present, steps = positive_int_diagnostic(record, "interpreter-steps")
        static_external_present, observed_static_externals = diagnostic_forms(
            record, "externals"
        )
        static_external_missing_present, reported_missing_static_externals = (
            diagnostic_forms(record, "missing-externals")
        )
        executed_external_present, observed_executed_externals = diagnostic_forms(
            record, "executed-externals"
        )
        executed_external_missing_present, reported_missing_executed_externals = (
            diagnostic_forms(record, "missing-executed-externals")
        )
        required_static = descriptor["requiredLcnfForms"]
        required_executed = descriptor["requiredExecutedLcnfForms"]
        required_static_externals = descriptor["requiredExternals"]
        required_executed_externals = descriptor["requiredExecutedExternals"]
        executed_obligations_active = bool(required_executed)
        static_external_obligations_active = bool(required_static_externals)
        executed_external_obligations_active = bool(required_executed_externals)
        missing_static = sorted(set(required_static) - set(observed_static))
        missing_executed = sorted(set(required_executed) - set(observed_executed))
        missing_static_externals = sorted(
            set(required_static_externals) - set(observed_static_externals)
        )
        missing_executed_externals = sorted(
            set(required_executed_externals) - set(observed_executed_externals)
        )

        static_required.update(required_static)
        static_observed.update(observed_static)
        executed_required.update(required_executed)
        executed_observed.update(observed_executed)
        static_missing_count += len(missing_static)
        executed_missing_count += len(missing_executed)
        executed_diagnostic_count += int(executed_present)
        executed_requirement_count += int(executed_obligations_active)
        static_external_required.update(required_static_externals)
        static_external_observed.update(observed_static_externals)
        executed_external_required.update(required_executed_externals)
        executed_external_observed.update(observed_executed_externals)
        static_external_missing_count += len(missing_static_externals)
        executed_external_missing_count += len(missing_executed_externals)
        static_external_diagnostic_count += int(static_external_present)
        executed_external_diagnostic_count += int(executed_external_present)
        static_external_missing_diagnostic_count += int(
            static_external_missing_present
        )
        executed_external_missing_diagnostic_count += int(
            executed_external_missing_present
        )
        static_external_requirement_count += int(static_external_obligations_active)
        executed_external_requirement_count += int(
            executed_external_obligations_active
        )
        if steps is not None:
            interpreter_steps.append(steps)

        if missing_static:
            failures.append(
                f"{case_id}: missing required static LCNF forms: "
                f"{','.join(missing_static)}"
            )
        if missing_executed:
            failures.append(
                f"{case_id}: missing required executed LCNF forms: "
                f"{','.join(missing_executed)}"
            )
        if missing_static_externals:
            failures.append(
                f"{case_id}: missing required static externals: "
                f"{','.join(missing_static_externals)}"
            )
        if missing_executed_externals:
            failures.append(
                f"{case_id}: missing required executed externals: "
                f"{','.join(missing_executed_externals)}"
            )
        if record is not None and not executed_present:
            failures.append(f"{case_id}: missing executed-lcnf-forms diagnostic")
        if record is not None and not steps_present:
            failures.append(f"{case_id}: missing interpreter-steps diagnostic")
        elif record is not None and steps is None:
            failures.append(f"{case_id}: interpreter-steps must be a positive integer")
        if record is not None and not static_external_present:
            failures.append(f"{case_id}: missing externals diagnostic")
        if record is not None and not static_external_missing_present:
            failures.append(f"{case_id}: missing missing-externals diagnostic")
        elif reported_missing_static_externals != missing_static_externals:
            failures.append(
                f"{case_id}: missing-externals diagnostic disagrees with obligations "
                f"(reported={','.join(reported_missing_static_externals)}; "
                f"computed={','.join(missing_static_externals)})"
            )
        if record is not None and not executed_external_present:
            failures.append(f"{case_id}: missing executed-externals diagnostic")
        if record is not None and not executed_external_missing_present:
            failures.append(f"{case_id}: missing missing-executed-externals diagnostic")
        elif reported_missing_executed_externals != missing_executed_externals:
            failures.append(
                f"{case_id}: missing-executed-externals diagnostic disagrees with "
                f"obligations (reported={','.join(reported_missing_executed_externals)}; "
                f"computed={','.join(missing_executed_externals)})"
            )

        cases.append(
            {
                "caseId": case_id,
                "static": {
                    "diagnosticPresent": static_present,
                    "requiredForms": required_static,
                    "observedForms": observed_static,
                    "missingRequiredForms": missing_static,
                },
                "executed": {
                    "diagnosticPresent": executed_present,
                    "obligationsActive": executed_obligations_active,
                    "requiredForms": required_executed,
                    "observedForms": observed_executed,
                    "missingRequiredForms": missing_executed,
                    "interpreterSteps": steps,
                },
                "externals": {
                    "static": {
                        "diagnosticPresent": static_external_present,
                        "missingDiagnosticPresent": static_external_missing_present,
                        "obligationsActive": static_external_obligations_active,
                        "requiredNames": required_static_externals,
                        "observedNames": observed_static_externals,
                        "missingRequiredNames": missing_static_externals,
                        "reportedMissingNames": reported_missing_static_externals,
                    },
                    "executed": {
                        "diagnosticPresent": executed_external_present,
                        "missingDiagnosticPresent": executed_external_missing_present,
                        "obligationsActive": executed_external_obligations_active,
                        "requiredNames": required_executed_externals,
                        "observedNames": observed_executed_externals,
                        "missingRequiredNames": missing_executed_externals,
                        "reportedMissingNames": reported_missing_executed_externals,
                    },
                },
            }
        )

    report = {
        "version": PROTOCOL_VERSION,
        "backend": "lcnf",
        "caseCount": len(cases),
        "summary": {
            "static": {
                "requiredForms": sorted(static_required),
                "observedForms": sorted(static_observed),
                "missingObligationCount": static_missing_count,
            },
            "executed": {
                "casesWithRequirements": executed_requirement_count,
                "casesWithDiagnostics": executed_diagnostic_count,
                "requiredForms": sorted(executed_required),
                "observedForms": sorted(executed_observed),
                "missingObligationCount": executed_missing_count,
                "totalInterpreterSteps": sum(interpreter_steps),
                "minimumInterpreterSteps": min(interpreter_steps, default=None),
                "maximumInterpreterSteps": max(interpreter_steps, default=None),
            },
            "externals": {
                "static": {
                    "casesWithRequirements": static_external_requirement_count,
                    "casesWithDiagnostics": static_external_diagnostic_count,
                    "casesWithMissingDiagnostics": (
                        static_external_missing_diagnostic_count
                    ),
                    "requiredNames": sorted(static_external_required),
                    "observedNames": sorted(static_external_observed),
                    "missingObligationCount": static_external_missing_count,
                },
                "executed": {
                    "casesWithRequirements": executed_external_requirement_count,
                    "casesWithDiagnostics": executed_external_diagnostic_count,
                    "casesWithMissingDiagnostics": (
                        executed_external_missing_diagnostic_count
                    ),
                    "requiredNames": sorted(executed_external_required),
                    "observedNames": sorted(executed_external_observed),
                    "missingObligationCount": executed_external_missing_count,
                },
            },
        },
        "cases": cases,
    }
    return report, failures


def write_coverage_artifact(out_dir: Path, report: dict) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "coverage.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def success_observation(record: dict) -> dict:
    case_id, outcome = checked_record(record, str(record["backend"]))
    success = outcome.get("success")
    if not isinstance(success, dict) or not isinstance(success.get("observation"), dict):
        status = next(iter(outcome))
        raise ValidationError(f"{record['backend']}/{case_id}: backend status is {status}")
    return success["observation"]


def compare_success(reference: dict, candidate: dict) -> tuple[bool, dict, dict]:
    reference_observation = success_observation(reference)
    candidate_observation = success_observation(candidate)
    return (
        reference_observation == candidate_observation,
        reference_observation,
        candidate_observation,
    )


def result_domain_failures(
    results: dict[str, dict], backend: str, expected_cases: list[str]
) -> list[str]:
    """Check which case IDs a backend returned, independently of how it ran."""
    expected = set(expected_cases)
    actual = set(results)
    failures: list[str] = []
    unknown = sorted(actual - expected)
    missing = sorted(expected - actual)
    if unknown:
        failures.append(
            f"{backend} backend returned unknown cases: {', '.join(unknown)}"
        )
    if missing:
        failures.append(f"{backend} backend omitted cases: {', '.join(missing)}")
    return failures


def compare_backend_results(
    descriptor_by_id: dict[str, dict],
    selected: list[str],
    reference_backend: str,
    reference_results: dict[str, dict],
    candidate_backend: str,
    candidate_results: dict[str, dict],
    blocked_cases: set[str] | None = None,
) -> tuple[list[dict], list[str]]:
    """Compare semantic observations without imposing candidate-specific policy."""
    blocked = blocked_cases or set()
    comparisons: list[dict] = []
    failures: list[str] = []
    for case_id in selected:
        if case_id in blocked:
            continue
        reference = reference_results.get(case_id)
        if reference is None:
            failures.append(f"{case_id}: {reference_backend} backend returned no result")
            continue
        candidate = candidate_results.get(case_id)
        if candidate is None:
            failures.append(f"{case_id}: {candidate_backend} backend returned no result")
            continue
        try:
            equal, reference_observation, candidate_observation = compare_success(
                reference, candidate
            )
        except ValidationError as error:
            failures.append(str(error))
            continue
        comparisons.append(
            {
                "caseId": case_id,
                "reference": reference_backend,
                "candidate": candidate_backend,
                "equal": equal,
                "case": descriptor_by_id[case_id],
            }
        )
        if not equal:
            failures.append(
                f"{case_id}: semantic mismatch\n"
                f"  {reference_backend}="
                f"{json.dumps(reference_observation, sort_keys=True)}\n"
                f"  {candidate_backend}="
                f"{json.dumps(candidate_observation, sort_keys=True)}"
            )
    return comparisons, failures


def write_artifact(out_dir: Path, case_id: str, backend: str, record: dict) -> None:
    destination = out_dir / case_id / backend
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "result.json").write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def write_process_artifacts(
    destination: Path, completed: subprocess.CompletedProcess[str]
) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "stdout.jsonl").write_text(completed.stdout, encoding="utf-8")
    (destination / "stderr.log").write_text(completed.stderr, encoding="utf-8")


def write_comparison_artifact(
    out_dir: Path,
    reference_backend: str,
    candidate_backend: str,
    comparisons: list[dict],
) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "comparison.json").write_text(
        json.dumps(
            {
                "version": PROTOCOL_VERSION,
                "reference": reference_backend,
                "candidate": candidate_backend,
                "comparisons": comparisons,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


@dataclass(frozen=True)
class BuildContext:
    root: Path
    out_dir: Path
    no_build: bool


@dataclass(frozen=True)
class RunContext:
    root: Path
    out_dir: Path
    descriptors: list[dict]
    selected: list[str]

    @property
    def all_cases(self) -> list[str]:
        return [descriptor["id"] for descriptor in self.descriptors]

    @property
    def descriptor_by_id(self) -> dict[str, dict]:
        return {descriptor["id"]: descriptor for descriptor in self.descriptors}


@dataclass
class BackendRun:
    backend: str
    expected_cases: list[str]
    results: dict[str, dict] = field(default_factory=dict)
    failures: list[str] = field(default_factory=list)
    blocked_cases: set[str] = field(default_factory=set)


@dataclass
class BackendAudit:
    report: dict | None = None
    failures: list[str] = field(default_factory=list)


class BackendAdapter(Protocol):
    name: str

    def build(self, context: BuildContext) -> None:
        ...

    def execute(self, context: RunContext) -> BackendRun:
        ...

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        ...


class NativeAdapter:
    name = "native"

    def build(self, context: BuildContext) -> None:
        if context.no_build:
            return
        built = run(["lake", "build", "fir-native-oracle"])
        if built.returncode != 0:
            sys.stderr.write(built.stdout + built.stderr)
            raise ValidationError("failed to build native validation backend")

    def execute(self, context: RunContext) -> BackendRun:
        backend_run = BackendRun(self.name, list(context.selected))
        for case_id in context.selected:
            command = ["lake", "exe", "fir-native-oracle", "--case", case_id]
            completed = run(command)
            write_process_artifacts(
                context.out_dir / case_id / self.name, completed
            )
            if completed.returncode != 0:
                backend_run.failures.append(
                    f"{case_id}: {self.name} process exited {completed.returncode}"
                )
                backend_run.blocked_cases.add(case_id)
                continue
            case_results = result_map(
                records_from_output(completed.stdout, command), self.name
            )
            if set(case_results) != {case_id}:
                backend_run.failures.append(
                    f"{case_id}: {self.name} backend returned {sorted(case_results)}"
                )
                backend_run.blocked_cases.add(case_id)
                continue
            backend_run.results[case_id] = case_results[case_id]
        return backend_run

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        return BackendAudit()


class LcnfAdapter:
    name = "lcnf"

    def build(self, context: BuildContext) -> None:
        if context.no_build:
            return
        built = run(["lake", "build", "Fir.Validation"])
        if built.returncode != 0:
            sys.stderr.write(built.stdout + built.stderr)
            raise ValidationError("failed to build LCNF validation backend")

    def execute(self, context: RunContext) -> BackendRun:
        command = ["lake", "env", "lean", "FirValidationLCNF.lean"]
        completed = run(command)
        write_process_artifacts(context.out_dir / self.name, completed)
        backend_run = BackendRun(self.name, context.all_cases)
        if completed.returncode != 0:
            backend_run.failures.append(
                f"{self.name} process exited {completed.returncode}"
            )
            backend_run.blocked_cases.update(context.selected)
            return backend_run
        backend_run.results = result_map(
            records_from_output(completed.stdout, command), self.name
        )
        return backend_run

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        report, failures = coverage_report(
            context.descriptors, backend_run.results, context.selected
        )
        write_coverage_artifact(context.out_dir / self.name, report)
        return BackendAudit(report, failures)


@dataclass(frozen=True)
class ExternalCommandAdapter:
    """Protocol adapter driven by shell-free commands from a JSON config."""

    name: str
    run_command: list[str]
    result_domain: str
    build_command: list[str] = field(default_factory=list)
    timeout_seconds: int = 120

    def environment(self, out_dir: Path) -> dict[str, str]:
        return {
            "FIR_VALIDATION_BACKEND": self.name,
            "FIR_VALIDATION_OUT_DIR": str((out_dir / self.name).resolve()),
            "FIR_VALIDATION_PROTOCOL_VERSION": str(PROTOCOL_VERSION),
        }

    def build(self, context: BuildContext) -> None:
        if context.no_build or not self.build_command:
            return
        destination = context.out_dir / self.name / "build"
        destination.mkdir(parents=True, exist_ok=True)
        completed = run(
            self.build_command,
            self.timeout_seconds,
            self.environment(context.out_dir),
        )
        write_process_artifacts(destination, completed)
        if completed.returncode != 0:
            raise ValidationError(
                f"failed to build {self.name} validation backend; "
                f"see {destination}"
            )

    def execute(self, context: RunContext) -> BackendRun:
        destination = context.out_dir / self.name
        destination.mkdir(parents=True, exist_ok=True)
        environment = self.environment(context.out_dir)
        environment.update(
            {
                "FIR_VALIDATION_CASES": json.dumps(
                    context.selected, separators=(",", ":")
                ),
                "FIR_VALIDATION_CORPUS": str(
                    (context.out_dir / "corpus.json").resolve()
                ),
            }
        )
        completed = run(self.run_command, self.timeout_seconds, environment)
        write_process_artifacts(destination, completed)
        expected_cases = (
            context.selected
            if self.result_domain == "selected"
            else context.all_cases
        )
        backend_run = BackendRun(self.name, list(expected_cases))
        if completed.returncode != 0:
            backend_run.failures.append(
                f"{self.name} process exited {completed.returncode}"
            )
            backend_run.blocked_cases.update(context.selected)
            return backend_run
        backend_run.results = result_map(
            records_from_output(completed.stdout, self.run_command), self.name
        )
        return backend_run

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        return BackendAudit()


def external_adapter_from_config(path: Path) -> ExternalCommandAdapter:
    """Load a declarative external adapter while rejecting shell commands."""
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot read adapter config {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValidationError(f"adapter config {path}: expected a JSON object")
    required = {"name", "runCommand", "resultDomain"}
    optional = {"buildCommand", "timeoutSeconds"}
    missing = sorted(required - value.keys())
    unknown = sorted(value.keys() - required - optional)
    if missing:
        raise ValidationError(
            f"adapter config {path}: missing fields: {', '.join(missing)}"
        )
    if unknown:
        raise ValidationError(
            f"adapter config {path}: unknown fields: {', '.join(unknown)}"
        )

    name = value["name"]
    allowed_name_characters = "abcdefghijklmnopqrstuvwxyz0123456789-_"
    if (
        not isinstance(name, str)
        or not name
        or not name[0].isalpha()
        or any(character not in allowed_name_characters for character in name)
    ):
        raise ValidationError(
            f"adapter config {path}: name must use lowercase letters, digits, "
            "'-' or '_'"
        )

    def checked_command(field_name: str, required_command: bool) -> list[str]:
        command = value.get(field_name, [])
        if (
            not isinstance(command, list)
            or (required_command and not command)
            or not all(isinstance(argument, str) and argument for argument in command)
        ):
            requirement = "a nonempty" if required_command else "an"
            raise ValidationError(
                f"adapter config {path}: {field_name} must be {requirement} argv array"
            )
        return list(command)

    run_command = checked_command("runCommand", True)
    build_command = checked_command("buildCommand", False)
    result_domain = value["resultDomain"]
    if result_domain not in ("selected", "corpus"):
        raise ValidationError(
            f"adapter config {path}: resultDomain must be 'selected' or 'corpus'"
        )
    timeout_seconds = value.get("timeoutSeconds", 120)
    if (
        not isinstance(timeout_seconds, int)
        or isinstance(timeout_seconds, bool)
        or timeout_seconds <= 0
    ):
        raise ValidationError(
            f"adapter config {path}: timeoutSeconds must be a positive integer"
        )
    return ExternalCommandAdapter(
        name,
        run_command,
        result_domain,
        build_command,
        timeout_seconds,
    )


BACKEND_ADAPTERS: dict[str, BackendAdapter] = {
    "native": NativeAdapter(),
    "lcnf": LcnfAdapter(),
}


def corpus_manifest() -> list[dict]:
    command = ["lake", "exe", "fir-native-oracle", "--manifest"]
    completed = run(command)
    if completed.returncode != 0:
        raise ValidationError(f"failed to read corpus manifest:\n{completed.stderr}")
    return manifest_from_output(completed.stdout, command)


def validate_pair(
    context: RunContext,
    reference: BackendAdapter,
    candidate: BackendAdapter,
) -> tuple[list[dict], list[str]]:
    """Execute, audit, persist, and compare one reference/candidate pair."""
    reference_run = reference.execute(context)
    candidate_run = candidate.execute(context)
    failures = list(reference_run.failures) + list(candidate_run.failures)
    failures.extend(
        result_domain_failures(
            reference_run.results, reference.name, reference_run.expected_cases
        )
    )
    failures.extend(
        result_domain_failures(
            candidate_run.results, candidate.name, candidate_run.expected_cases
        )
    )

    for case_id in context.selected:
        for backend_run in (reference_run, candidate_run):
            record = backend_run.results.get(case_id)
            if record is not None:
                write_artifact(context.out_dir, case_id, backend_run.backend, record)

    reference_audit = reference.audit(context, reference_run)
    candidate_audit = candidate.audit(context, candidate_run)
    failures.extend(reference_audit.failures)
    failures.extend(candidate_audit.failures)

    comparisons, comparison_failures = compare_backend_results(
        context.descriptor_by_id,
        context.selected,
        reference.name,
        reference_run.results,
        candidate.name,
        candidate_run.results,
        reference_run.blocked_cases | candidate_run.blocked_cases,
    )
    failures.extend(comparison_failures)
    write_comparison_artifact(
        context.out_dir, reference.name, candidate.name, comparisons
    )
    return comparisons, failures


def main() -> int:
    parser = argparse.ArgumentParser(
        description="compare protocol observations from two validation backends"
    )
    parser.add_argument("--case", action="append", dest="cases", help="run only this case ID")
    parser.add_argument("--tag", help="run cases carrying this corpus tag")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="reuse existing backend builds",
    )
    parser.add_argument(
        "--reference",
        default="native",
        help="backend supplying the reference observation",
    )
    parser.add_argument(
        "--candidate",
        default="lcnf",
        help="backend whose observation is checked",
    )
    parser.add_argument(
        "--adapter-config",
        action="append",
        type=Path,
        default=[],
        help="register an external protocol backend from this JSON file",
    )
    args = parser.parse_args()

    if args.reference == args.candidate:
        raise ValidationError("reference and candidate backends must differ")
    adapters = dict(BACKEND_ADAPTERS)
    for path in args.adapter_config:
        adapter = external_adapter_from_config(path)
        if adapter.name in adapters:
            raise ValidationError(
                f"backend registered more than once: {adapter.name}"
            )
        adapters[adapter.name] = adapter
    unknown_backends = sorted({args.reference, args.candidate} - adapters.keys())
    if unknown_backends:
        raise ValidationError(
            "unknown validation backend(s): "
            f"{', '.join(unknown_backends)}; registered: {', '.join(sorted(adapters))}"
        )
    reference = adapters[args.reference]
    candidate = adapters[args.candidate]
    build_context = BuildContext(ROOT, args.out_dir, args.no_build)
    adapters_to_build = {
        adapter.name: adapter
        for adapter in (adapters["native"], reference, candidate)
    }
    for adapter in adapters_to_build.values():
        adapter.build(build_context)

    descriptors = corpus_manifest()
    selected = select_cases(descriptors, args.cases, args.tag)
    write_corpus_manifest(args.out_dir, descriptors)
    context = RunContext(ROOT, args.out_dir, descriptors, selected)
    comparisons, failures = validate_pair(context, reference, candidate)
    for comparison in comparisons:
        if comparison["equal"]:
            case_id = comparison["caseId"]
            print(f"PASS {case_id:<22} {reference.name} == {candidate.name}")

    if failures:
        for failure in failures:
            print(f"FAIL {failure}", file=sys.stderr)
        return 1
    print(
        f"validated {len(selected)} case(s): "
        f"{reference.name} == {candidate.name}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validation harness error: {error}", file=sys.stderr)
        raise SystemExit(2)
