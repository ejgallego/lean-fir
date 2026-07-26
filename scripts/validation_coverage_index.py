#!/usr/bin/env python3
"""Compose verified validation matrices into a tier-aware coverage index."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from validation_harness import (
    PROTOCOL_VERSION,
    ValidationError,
    canonical_json_sha256,
    sha256_bytes,
    validate_backend_name,
    verify_matrix_artifact,
)


ROOT = Path(__file__).resolve().parents[1]


def _read_json(path: Path, context: str) -> tuple[dict, bytes]:
    try:
        content = path.read_bytes()
    except OSError as error:
        raise ValidationError(f"cannot read {context} {path}: {error}") from error
    try:
        value = json.loads(content)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot parse {context} {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValidationError(f"{context} {path} must be a JSON object")
    return value, content


def _checked_nat(value: object, context: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValidationError(f"{context} must be a natural number")
    return value


def _checked_string_list(value: object, context: str) -> list[str]:
    if (
        not isinstance(value, list)
        or not all(isinstance(item, str) and item for item in value)
        or value != sorted(set(value))
    ):
        raise ValidationError(
            f"{context} must be a sorted array of unique nonempty strings"
        )
    return list(value)


def _checked_named_counts(
    value: object,
    name_field: str,
    count_field: str,
    context: str,
) -> list[dict]:
    if not isinstance(value, list):
        raise ValidationError(f"{context} must be an array")
    checked: list[dict] = []
    for item in value:
        if (
            not isinstance(item, dict)
            or set(item) != {name_field, count_field}
            or not isinstance(item[name_field], str)
            or not item[name_field]
        ):
            raise ValidationError(f"{context} contains a malformed count")
        checked.append(
            {
                name_field: item[name_field],
                count_field: _checked_nat(
                    item[count_field],
                    f"{context}/{item[name_field]}/{count_field}",
                ),
            }
        )
    if [item[name_field] for item in checked] != sorted(
        {item[name_field] for item in checked}
    ):
        raise ValidationError(f"{context} must be sorted with unique names")
    return checked


def _checked_dict(value: object, context: str) -> dict:
    if not isinstance(value, dict):
        raise ValidationError(f"{context} must be an object")
    return value


def _resolved_input(
    raw_path: object,
    plan_path: Path,
    root: Path,
    context: str,
) -> tuple[Path, str]:
    if not isinstance(raw_path, str) or not raw_path or Path(raw_path).is_absolute():
        raise ValidationError(f"{context} must be a nonempty relative path")
    resolved = (plan_path.parent / raw_path).resolve()
    try:
        name = resolved.relative_to(root.resolve()).as_posix()
    except ValueError as error:
        raise ValidationError(f"{context} escapes the repository root") from error
    return resolved, name


def _sum_named_counts(
    groups: list[list[dict]],
    name_field: str,
    count_field: str,
) -> list[dict]:
    totals: dict[str, int] = {}
    for group in groups:
        for item in group:
            totals[item[name_field]] = totals.get(item[name_field], 0) + item[
                count_field
            ]
    return [
        {name_field: name, count_field: totals[name]}
        for name in sorted(totals)
    ]


def machine_coverage_summary(
    report: dict,
    matrix: dict,
    context: str,
) -> dict:
    """Validate and retain the aggregate portions of one LCNF coverage report."""
    if set(report) != {"version", "backend", "caseCount", "summary", "cases"}:
        raise ValidationError(f"{context} has an unsupported top-level schema")
    if report["version"] != PROTOCOL_VERSION or isinstance(
        report["version"], bool
    ):
        raise ValidationError(f"{context} has an unsupported version")
    backend = validate_backend_name(report["backend"], f"{context} backend")
    if backend not in matrix["backends"]:
        raise ValidationError(f"{context} backend is absent from its matrix")
    case_count = _checked_nat(report["caseCount"], f"{context} caseCount")
    selected_cases = matrix["selectedCases"]
    if case_count != len(selected_cases):
        raise ValidationError(f"{context} case count disagrees with its matrix")
    cases = report["cases"]
    if not isinstance(cases, list) or not all(isinstance(case, dict) for case in cases):
        raise ValidationError(f"{context} cases must be an array of objects")
    case_ids = [case.get("caseId") for case in cases]
    if case_ids != selected_cases:
        raise ValidationError(f"{context} case domain disagrees with its matrix")

    summary = _checked_dict(report["summary"], f"{context}/summary")
    static = _checked_dict(summary.get("static"), f"{context}/summary/static")
    executed = _checked_dict(
        summary.get("executed"), f"{context}/summary/executed"
    )
    form_counts = _checked_dict(
        executed.get("formCounts"), f"{context}/summary/executed/formCounts"
    )
    form_trace = _checked_dict(
        executed.get("formTrace"), f"{context}/summary/executed/formTrace"
    )
    step_trace = _checked_dict(
        executed.get("stepTrace"), f"{context}/summary/executed/stepTrace"
    )
    externals = _checked_dict(
        summary.get("externals"), f"{context}/summary/externals"
    )
    static_externals = _checked_dict(
        externals.get("static"), f"{context}/summary/externals/static"
    )
    executed_externals = _checked_dict(
        externals.get("executed"), f"{context}/summary/externals/executed"
    )
    external_counts = _checked_dict(
        executed_externals.get("counts"),
        f"{context}/summary/externals/executed/counts",
    )
    external_trace = _checked_dict(
        executed_externals.get("trace"),
        f"{context}/summary/externals/executed/trace",
    )

    static_missing = _checked_nat(
        static.get("missingObligationCount"),
        f"{context}/summary/static/missingObligationCount",
    )
    executed_missing = _checked_nat(
        executed.get("missingObligationCount"),
        f"{context}/summary/executed/missingObligationCount",
    )
    form_count_missing = _checked_nat(
        form_counts.get("unsatisfiedObligationCount"),
        f"{context}/summary/executed/formCounts/unsatisfiedObligationCount",
    )
    form_trace_mismatches = _checked_nat(
        form_trace.get("mismatchedObligationCount"),
        f"{context}/summary/executed/formTrace/mismatchedObligationCount",
    )
    administrative_missing = _checked_nat(
        step_trace.get("missingAdministrativeObligationCount"),
        f"{context}/summary/executed/stepTrace/"
        "missingAdministrativeObligationCount",
    )
    static_external_missing = _checked_nat(
        static_externals.get("missingObligationCount"),
        f"{context}/summary/externals/static/missingObligationCount",
    )
    executed_external_missing = _checked_nat(
        executed_externals.get("missingObligationCount"),
        f"{context}/summary/externals/executed/missingObligationCount",
    )
    external_count_missing = _checked_nat(
        external_counts.get("unsatisfiedObligationCount"),
        f"{context}/summary/externals/executed/counts/"
        "unsatisfiedObligationCount",
    )
    external_trace_mismatches = _checked_nat(
        external_trace.get("mismatchedObligationCount"),
        f"{context}/summary/externals/executed/trace/"
        "mismatchedObligationCount",
    )
    unclassified_steps = _checked_nat(
        step_trace.get("unclassifiedStepCount"),
        f"{context}/summary/executed/stepTrace/unclassifiedStepCount",
    )

    diagnostic_gaps = sum(
        case_count
        - _checked_nat(value, f"{context}/{name}")
        for name, value in (
            (
                "executed/formCounts/casesWithValidDiagnostics",
                form_counts.get("casesWithValidDiagnostics"),
            ),
            (
                "executed/formTrace/casesWithValidDiagnostics",
                form_trace.get("casesWithValidDiagnostics"),
            ),
            (
                "executed/stepTrace/casesWithValidDiagnostics",
                step_trace.get("casesWithValidDiagnostics"),
            ),
            (
                "executed/stepTrace/casesWithCompleteCoverage",
                step_trace.get("casesWithCompleteCoverage"),
            ),
            (
                "externals/executed/counts/casesWithValidDiagnostics",
                external_counts.get("casesWithValidDiagnostics"),
            ),
            (
                "externals/executed/trace/casesWithValidDiagnostics",
                external_trace.get("casesWithValidDiagnostics"),
            ),
        )
    )
    if diagnostic_gaps < 0:
        raise ValidationError(f"{context} reports more diagnostics than cases")

    obligation_failure_count = sum(
        (
            static_missing,
            executed_missing,
            form_count_missing,
            form_trace_mismatches,
            administrative_missing,
            static_external_missing,
            executed_external_missing,
            external_count_missing,
            external_trace_mismatches,
        )
    )
    telemetry_failure_count = diagnostic_gaps + unclassified_steps
    return {
        "backend": backend,
        "caseCount": case_count,
        "forms": {
            "staticObserved": _checked_string_list(
                static.get("observedForms"), f"{context}/static observed forms"
            ),
            "staticRequired": _checked_string_list(
                static.get("requiredForms"), f"{context}/static required forms"
            ),
            "executedObserved": _checked_string_list(
                executed.get("observedForms"),
                f"{context}/executed observed forms",
            ),
            "executedRequired": _checked_string_list(
                executed.get("requiredForms"),
                f"{context}/executed required forms",
            ),
            "observedCounts": _checked_named_counts(
                form_counts.get("observed"),
                "form",
                "count",
                f"{context}/executed form counts",
            ),
            "requiredMinimums": _checked_named_counts(
                form_counts.get("requiredMinimums"),
                "form",
                "minimum",
                f"{context}/executed form minimums",
            ),
        },
        "steps": {
            "interpreterStepCount": _checked_nat(
                executed.get("totalInterpreterSteps"),
                f"{context}/totalInterpreterSteps",
            ),
            "observedAdministrativeKinds": _checked_named_counts(
                step_trace.get("administrativeKinds"),
                "kind",
                "count",
                f"{context}/administrative kinds",
            ),
            "requiredAdministrativeKinds": _checked_string_list(
                step_trace.get("requiredAdministrativeKinds"),
                f"{context}/required administrative kinds",
            ),
            "unobservedAdministrativeKinds": _checked_string_list(
                step_trace.get("unobservedAdministrativeKinds"),
                f"{context}/unobserved administrative kinds",
            ),
        },
        "externals": {
            "staticObserved": _checked_string_list(
                static_externals.get("observedNames"),
                f"{context}/static observed externals",
            ),
            "staticRequired": _checked_string_list(
                static_externals.get("requiredNames"),
                f"{context}/static required externals",
            ),
            "executedObserved": _checked_string_list(
                executed_externals.get("observedNames"),
                f"{context}/executed observed externals",
            ),
            "executedRequired": _checked_string_list(
                executed_externals.get("requiredNames"),
                f"{context}/executed required externals",
            ),
            "observedCounts": _checked_named_counts(
                external_counts.get("observed"),
                "external",
                "count",
                f"{context}/executed external counts",
            ),
            "requiredMinimums": _checked_named_counts(
                external_counts.get("requiredMinimums"),
                "external",
                "minimum",
                f"{context}/executed external minimums",
            ),
        },
        "obligationFailureCount": obligation_failure_count,
        "telemetryFailureCount": telemetry_failure_count,
        "complete": obligation_failure_count == 0 and telemetry_failure_count == 0,
    }


def aggregate_machine_coverage(coverages: list[dict]) -> dict:
    observed_administrative = {
        item["kind"]
        for coverage in coverages
        for item in coverage["steps"]["observedAdministrativeKinds"]
    }
    recognized_administrative = {
        *observed_administrative,
        *(
            kind
            for coverage in coverages
            for kind in coverage["steps"]["unobservedAdministrativeKinds"]
        ),
    }
    return {
        "coverageTierCount": len(coverages),
        "caseCount": sum(coverage["caseCount"] for coverage in coverages),
        "forms": {
            "staticObserved": sorted(
                {
                    form
                    for coverage in coverages
                    for form in coverage["forms"]["staticObserved"]
                }
            ),
            "staticRequired": sorted(
                {
                    form
                    for coverage in coverages
                    for form in coverage["forms"]["staticRequired"]
                }
            ),
            "executedObserved": sorted(
                {
                    form
                    for coverage in coverages
                    for form in coverage["forms"]["executedObserved"]
                }
            ),
            "executedRequired": sorted(
                {
                    form
                    for coverage in coverages
                    for form in coverage["forms"]["executedRequired"]
                }
            ),
            "observedCounts": _sum_named_counts(
                [coverage["forms"]["observedCounts"] for coverage in coverages],
                "form",
                "count",
            ),
            "requiredMinimums": _sum_named_counts(
                [
                    coverage["forms"]["requiredMinimums"]
                    for coverage in coverages
                ],
                "form",
                "minimum",
            ),
        },
        "steps": {
            "interpreterStepCount": sum(
                coverage["steps"]["interpreterStepCount"]
                for coverage in coverages
            ),
            "observedAdministrativeKinds": _sum_named_counts(
                [
                    coverage["steps"]["observedAdministrativeKinds"]
                    for coverage in coverages
                ],
                "kind",
                "count",
            ),
            "requiredAdministrativeKinds": sorted(
                {
                    kind
                    for coverage in coverages
                    for kind in coverage["steps"]["requiredAdministrativeKinds"]
                }
            ),
            "unobservedAdministrativeKinds": sorted(
                recognized_administrative - observed_administrative
            ),
        },
        "externals": {
            "staticObserved": sorted(
                {
                    name
                    for coverage in coverages
                    for name in coverage["externals"]["staticObserved"]
                }
            ),
            "staticRequired": sorted(
                {
                    name
                    for coverage in coverages
                    for name in coverage["externals"]["staticRequired"]
                }
            ),
            "executedObserved": sorted(
                {
                    name
                    for coverage in coverages
                    for name in coverage["externals"]["executedObserved"]
                }
            ),
            "executedRequired": sorted(
                {
                    name
                    for coverage in coverages
                    for name in coverage["externals"]["executedRequired"]
                }
            ),
            "observedCounts": _sum_named_counts(
                [
                    coverage["externals"]["observedCounts"]
                    for coverage in coverages
                ],
                "external",
                "count",
            ),
            "requiredMinimums": _sum_named_counts(
                [
                    coverage["externals"]["requiredMinimums"]
                    for coverage in coverages
                ],
                "external",
                "minimum",
            ),
        },
        "obligationFailureCount": sum(
            coverage["obligationFailureCount"] for coverage in coverages
        ),
        "telemetryFailureCount": sum(
            coverage["telemetryFailureCount"] for coverage in coverages
        ),
        "complete": all(coverage["complete"] for coverage in coverages),
    }


def coverage_policy_report(
    raw_policy: object,
    tiers: list[dict],
    summary: dict,
) -> dict:
    """Evaluate monotone coverage floors declared by the composition plan."""
    if not isinstance(raw_policy, dict) or set(raw_policy) != {
        "tiers",
        "aggregate",
        "machine",
    }:
        raise ValidationError(
            "coverage index policy requires tiers, aggregate, and machine"
        )
    raw_tier_policies = raw_policy["tiers"]
    if not isinstance(raw_tier_policies, list):
        raise ValidationError("coverage index tier policy must be an array")
    if len(raw_tier_policies) != len(tiers):
        raise ValidationError(
            "coverage index tier policy must cover every tier exactly once"
        )

    tier_reports: list[dict] = []
    for raw_requirement, tier in zip(raw_tier_policies, tiers):
        if not isinstance(raw_requirement, dict) or set(raw_requirement) != {
            "id",
            "minimumCases",
            "minimumComparisons",
            "requiredBackends",
            "requireMachineCoverage",
        }:
            raise ValidationError(
                "coverage index tier policy entries require id, minimumCases, "
                "minimumComparisons, requiredBackends, and "
                "requireMachineCoverage"
            )
        tier_id = validate_backend_name(
            raw_requirement["id"], "coverage policy tier id"
        )
        if tier_id != tier["id"]:
            raise ValidationError(
                "coverage index tier policy order must match tier order"
            )
        minimum_cases = _checked_nat(
            raw_requirement["minimumCases"],
            f"coverage policy tier {tier_id} minimumCases",
        )
        minimum_comparisons = _checked_nat(
            raw_requirement["minimumComparisons"],
            f"coverage policy tier {tier_id} minimumComparisons",
        )
        required_backends = _checked_string_list(
            raw_requirement["requiredBackends"],
            f"coverage policy tier {tier_id} requiredBackends",
        )
        for backend in required_backends:
            validate_backend_name(
                backend, f"coverage policy tier {tier_id} backend"
            )
        require_machine = raw_requirement["requireMachineCoverage"]
        if not isinstance(require_machine, bool):
            raise ValidationError(
                f"coverage policy tier {tier_id} "
                "requireMachineCoverage must be Boolean"
            )

        observed_backends = sorted(
            item["backend"] for item in tier["backends"]
        )
        observed_comparisons = sum(
            _checked_nat(
                item["comparedCases"],
                f"coverage policy tier {tier_id} compared cases",
            )
            for item in tier["pairs"]
        )
        case_deficit = max(0, minimum_cases - tier["caseCount"])
        comparison_deficit = max(
            0, minimum_comparisons - observed_comparisons
        )
        missing_backends = sorted(
            set(required_backends) - set(observed_backends)
        )
        missing_machine = (
            require_machine and tier["machineCoverage"] is None
        )
        failure_count = sum(
            (
                int(case_deficit > 0),
                int(comparison_deficit > 0),
                int(bool(missing_backends)),
                int(missing_machine),
            )
        )
        tier_reports.append(
            {
                "id": tier_id,
                "minimumCases": minimum_cases,
                "observedCases": tier["caseCount"],
                "caseDeficit": case_deficit,
                "minimumComparisons": minimum_comparisons,
                "observedComparisons": observed_comparisons,
                "comparisonDeficit": comparison_deficit,
                "requiredBackends": required_backends,
                "observedBackends": observed_backends,
                "missingBackends": missing_backends,
                "requireMachineCoverage": require_machine,
                "machineCoveragePresent": tier["machineCoverage"] is not None,
                "failureCount": failure_count,
                "satisfied": failure_count == 0,
            }
        )

    raw_aggregate = raw_policy["aggregate"]
    if not isinstance(raw_aggregate, dict) or set(raw_aggregate) != {
        "minimumUniqueCases",
        "minimumTierCases",
        "minimumComparisons",
    }:
        raise ValidationError(
            "coverage index aggregate policy requires minimumUniqueCases, "
            "minimumTierCases, and minimumComparisons"
        )
    minimum_unique_cases = _checked_nat(
        raw_aggregate["minimumUniqueCases"],
        "coverage aggregate policy minimumUniqueCases",
    )
    minimum_tier_cases = _checked_nat(
        raw_aggregate["minimumTierCases"],
        "coverage aggregate policy minimumTierCases",
    )
    minimum_comparisons = _checked_nat(
        raw_aggregate["minimumComparisons"],
        "coverage aggregate policy minimumComparisons",
    )
    unique_case_deficit = max(
        0, minimum_unique_cases - summary["uniqueCaseCount"]
    )
    tier_case_deficit = max(
        0, minimum_tier_cases - summary["tierCaseCount"]
    )
    comparison_deficit = max(
        0, minimum_comparisons - summary["comparisonCount"]
    )
    aggregate_failure_count = sum(
        (
            int(unique_case_deficit > 0),
            int(tier_case_deficit > 0),
            int(comparison_deficit > 0),
        )
    )
    aggregate_report = {
        "minimumUniqueCases": minimum_unique_cases,
        "observedUniqueCases": summary["uniqueCaseCount"],
        "uniqueCaseDeficit": unique_case_deficit,
        "minimumTierCases": minimum_tier_cases,
        "observedTierCases": summary["tierCaseCount"],
        "tierCaseDeficit": tier_case_deficit,
        "minimumComparisons": minimum_comparisons,
        "observedComparisons": summary["comparisonCount"],
        "comparisonDeficit": comparison_deficit,
        "failureCount": aggregate_failure_count,
        "satisfied": aggregate_failure_count == 0,
    }

    raw_machine = raw_policy["machine"]
    if not isinstance(raw_machine, dict) or set(raw_machine) != {
        "minimumCases",
        "minimumInterpreterSteps",
        "requiredStaticForms",
        "requiredExecutedForms",
        "requiredAdministrativeKinds",
        "requiredExternals",
    }:
        raise ValidationError(
            "coverage index machine policy requires minimumCases, "
            "minimumInterpreterSteps, requiredStaticForms, "
            "requiredExecutedForms, requiredAdministrativeKinds, and "
            "requiredExternals"
        )
    minimum_machine_cases = _checked_nat(
        raw_machine["minimumCases"],
        "coverage machine policy minimumCases",
    )
    minimum_steps = _checked_nat(
        raw_machine["minimumInterpreterSteps"],
        "coverage machine policy minimumInterpreterSteps",
    )
    required_static_forms = _checked_string_list(
        raw_machine["requiredStaticForms"],
        "coverage machine policy requiredStaticForms",
    )
    required_executed_forms = _checked_string_list(
        raw_machine["requiredExecutedForms"],
        "coverage machine policy requiredExecutedForms",
    )
    required_administrative = _checked_string_list(
        raw_machine["requiredAdministrativeKinds"],
        "coverage machine policy requiredAdministrativeKinds",
    )
    required_externals = _checked_string_list(
        raw_machine["requiredExternals"],
        "coverage machine policy requiredExternals",
    )
    machine = summary["machine"]
    observed_static_forms = machine["forms"]["staticObserved"]
    observed_executed_forms = machine["forms"]["executedObserved"]
    observed_administrative = [
        item["kind"] for item in machine["steps"]["observedAdministrativeKinds"]
    ]
    observed_externals = machine["externals"]["executedObserved"]
    machine_case_deficit = max(
        0, minimum_machine_cases - machine["caseCount"]
    )
    step_deficit = max(
        0, minimum_steps - machine["steps"]["interpreterStepCount"]
    )
    missing_static_forms = sorted(
        set(required_static_forms) - set(observed_static_forms)
    )
    missing_executed_forms = sorted(
        set(required_executed_forms) - set(observed_executed_forms)
    )
    missing_administrative = sorted(
        set(required_administrative) - set(observed_administrative)
    )
    missing_externals = sorted(
        set(required_externals) - set(observed_externals)
    )
    machine_failure_count = sum(
        (
            int(machine_case_deficit > 0),
            int(step_deficit > 0),
            int(bool(missing_static_forms)),
            int(bool(missing_executed_forms)),
            int(bool(missing_administrative)),
            int(bool(missing_externals)),
        )
    )
    machine_report = {
        "minimumCases": minimum_machine_cases,
        "observedCases": machine["caseCount"],
        "caseDeficit": machine_case_deficit,
        "minimumInterpreterSteps": minimum_steps,
        "observedInterpreterSteps": machine["steps"]["interpreterStepCount"],
        "interpreterStepDeficit": step_deficit,
        "requiredStaticForms": required_static_forms,
        "observedStaticForms": observed_static_forms,
        "missingStaticForms": missing_static_forms,
        "requiredExecutedForms": required_executed_forms,
        "observedExecutedForms": observed_executed_forms,
        "missingExecutedForms": missing_executed_forms,
        "requiredAdministrativeKinds": required_administrative,
        "observedAdministrativeKinds": observed_administrative,
        "missingAdministrativeKinds": missing_administrative,
        "requiredExternals": required_externals,
        "observedExternals": observed_externals,
        "missingExternals": missing_externals,
        "failureCount": machine_failure_count,
        "satisfied": machine_failure_count == 0,
    }
    failure_count = (
        sum(report["failureCount"] for report in tier_reports)
        + aggregate_failure_count
        + machine_failure_count
    )
    return {
        "tiers": tier_reports,
        "aggregate": aggregate_report,
        "machine": machine_report,
        "failureCount": failure_count,
        "satisfied": failure_count == 0,
    }


def _tier_from_config(
    raw_tier: object,
    plan_path: Path,
    root: Path,
) -> tuple[dict, set[str]]:
    if not isinstance(raw_tier, dict) or set(raw_tier) != {
        "id",
        "kind",
        "matrix",
        "pairs",
        "machineCoverage",
    }:
        raise ValidationError(
            "coverage index tiers require id, kind, matrix, pairs, and "
            "machineCoverage"
        )
    tier_id = validate_backend_name(raw_tier["id"], "coverage tier id")
    kind = validate_backend_name(raw_tier["kind"], f"coverage tier {tier_id} kind")
    matrix_path, matrix_name = _resolved_input(
        raw_tier["matrix"], plan_path, root, f"coverage tier {tier_id} matrix"
    )
    matrix_value, matrix_content = _read_json(
        matrix_path, f"coverage tier {tier_id} matrix"
    )
    matrix = verify_matrix_artifact(matrix_path)
    if matrix != matrix_value:
        raise ValidationError(
            f"coverage tier {tier_id} verified matrix changed while indexing"
        )

    raw_pairs = raw_tier["pairs"]
    if not isinstance(raw_pairs, list) or not raw_pairs:
        raise ValidationError(f"coverage tier {tier_id} pairs must be nonempty")
    pair_names: list[tuple[str, str]] = []
    for raw_pair in raw_pairs:
        if not isinstance(raw_pair, dict) or set(raw_pair) != {
            "reference",
            "candidate",
        }:
            raise ValidationError(
                f"coverage tier {tier_id} contains a malformed pair"
            )
        pair_names.append(
            (
                validate_backend_name(
                    raw_pair["reference"], f"coverage tier {tier_id} reference"
                ),
                validate_backend_name(
                    raw_pair["candidate"], f"coverage tier {tier_id} candidate"
                ),
            )
        )
    if len(set(pair_names)) != len(pair_names):
        raise ValidationError(f"coverage tier {tier_id} repeats a pair")
    matrix_pairs = {
        (item["reference"], item["candidate"]): item for item in matrix["pairs"]
    }
    missing_pairs = [pair for pair in pair_names if pair not in matrix_pairs]
    if missing_pairs:
        raise ValidationError(
            f"coverage tier {tier_id} selects pairs absent from its matrix: "
            + ", ".join(
                f"{reference}->{candidate}"
                for reference, candidate in missing_pairs
            )
        )
    selected_pairs = [matrix_pairs[pair] for pair in pair_names]
    involved = {
        backend
        for reference, candidate in pair_names
        for backend in (reference, candidate)
    }
    matrix_coverage = _checked_dict(
        matrix.get("coverage"), f"coverage tier {tier_id} matrix coverage"
    )
    backend_coverage = {
        item["backend"]: item
        for item in matrix_coverage.get("backends", [])
        if isinstance(item, dict) and isinstance(item.get("backend"), str)
    }
    if not involved <= backend_coverage.keys():
        raise ValidationError(
            f"coverage tier {tier_id} matrix omits backend coverage"
        )
    selected_backend_coverage = [
        backend_coverage[backend]
        for backend in matrix["backends"]
        if backend in involved
    ]
    case_count = len(matrix["selectedCases"])
    semantic_complete = (
        _checked_nat(
            matrix_coverage.get("findingCount"),
            f"coverage tier {tier_id} findingCount",
        )
        == 0
        and all(
            _checked_nat(item.get("resultCaseCount"), f"{tier_id} backend results")
            == case_count
            and _checked_nat(
                item.get("successfulCaseCount"), f"{tier_id} backend successes"
            )
            == case_count
            and _checked_nat(item.get("findingCount"), f"{tier_id} backend findings")
            == 0
            for item in selected_backend_coverage
        )
        and all(
            _checked_nat(item.get("comparedCases"), f"{tier_id} compared cases")
            == case_count
            and _checked_nat(item.get("equalCases"), f"{tier_id} equal cases")
            == case_count
            and _checked_nat(item.get("findingCount"), f"{tier_id} pair findings")
            == 0
            for item in selected_pairs
        )
    )

    machine_input = None
    machine_coverage = None
    raw_machine_path = raw_tier["machineCoverage"]
    if raw_machine_path is not None:
        machine_path, machine_name = _resolved_input(
            raw_machine_path,
            plan_path,
            root,
            f"coverage tier {tier_id} machine coverage",
        )
        machine_report, machine_content = _read_json(
            machine_path, f"coverage tier {tier_id} machine coverage"
        )
        machine_input = {
            "name": machine_name,
            "sha256": sha256_bytes(machine_content),
        }
        machine_coverage = machine_coverage_summary(
            machine_report,
            matrix,
            f"coverage tier {tier_id} machine coverage",
        )

    complete = semantic_complete and (
        machine_coverage is None or machine_coverage["complete"]
    )
    return (
        {
            "id": tier_id,
            "kind": kind,
            "matrix": {
                "name": matrix_name,
                "sha256": sha256_bytes(matrix_content),
                "run": matrix["identity"]["run"],
                "selection": matrix["identity"]["selection"],
            },
            "caseIds": list(matrix["selectedCases"]),
            "caseCount": case_count,
            "backends": selected_backend_coverage,
            "pairs": selected_pairs,
            "providers": list(matrix_coverage.get("providers", [])),
            "consumers": list(matrix_coverage.get("consumers", [])),
            "findingCount": matrix_coverage["findingCount"],
            "machineCoverageInput": machine_input,
            "machineCoverage": machine_coverage,
            "complete": complete,
        },
        set(matrix["selectedCases"]),
    )


def build_coverage_index(plan_path: Path, root: Path = ROOT) -> dict:
    plan_path = plan_path.resolve()
    root = root.resolve()
    try:
        plan_name = plan_path.relative_to(root).as_posix()
    except ValueError as error:
        raise ValidationError(
            "coverage index plan escapes the repository root"
        ) from error
    plan, plan_content = _read_json(plan_path, "coverage index plan")
    if set(plan) != {"version", "tiers", "policy"}:
        raise ValidationError(
            "coverage index plan must contain exactly version, tiers, and policy"
        )
    if plan["version"] != PROTOCOL_VERSION or isinstance(plan["version"], bool):
        raise ValidationError("unsupported coverage index plan version")
    raw_tiers = plan["tiers"]
    if not isinstance(raw_tiers, list) or not raw_tiers:
        raise ValidationError("coverage index plan tiers must be nonempty")
    tiers: list[dict] = []
    case_domains: list[set[str]] = []
    for raw_tier in raw_tiers:
        tier, cases = _tier_from_config(raw_tier, plan_path, root)
        tiers.append(tier)
        case_domains.append(cases)
    tier_ids = [tier["id"] for tier in tiers]
    if len(set(tier_ids)) != len(tier_ids):
        raise ValidationError("coverage index plan repeats a tier id")

    machine_coverages = [
        tier["machineCoverage"]
        for tier in tiers
        if tier["machineCoverage"] is not None
    ]
    machine = aggregate_machine_coverage(machine_coverages)
    summary = {
        "tierCount": len(tiers),
        "tierCaseCount": sum(tier["caseCount"] for tier in tiers),
        "uniqueCaseCount": len(set().union(*case_domains)),
        "backendResultCount": sum(
            _checked_nat(item["resultCaseCount"], "tier backend results")
            for tier in tiers
            for item in tier["backends"]
        ),
        "successfulBackendResultCount": sum(
            _checked_nat(
                item["successfulCaseCount"], "tier backend successes"
            )
            for tier in tiers
            for item in tier["backends"]
        ),
        "comparisonCount": sum(
            _checked_nat(item["comparedCases"], "tier comparisons")
            for tier in tiers
            for item in tier["pairs"]
        ),
        "equalComparisonCount": sum(
            _checked_nat(item["equalCases"], "tier equal comparisons")
            for tier in tiers
            for item in tier["pairs"]
        ),
        "findingCount": sum(tier["findingCount"] for tier in tiers),
        "machine": machine,
    }
    policy = coverage_policy_report(plan["policy"], tiers, summary)
    summary["policyFailureCount"] = policy["failureCount"]
    summary["complete"] = (
        all(tier["complete"] for tier in tiers)
        and machine["complete"]
        and policy["satisfied"]
    )
    provisional = {
        "version": PROTOCOL_VERSION,
        "plan": {
            "name": plan_name,
            "sha256": sha256_bytes(plan_content),
        },
        "tiers": tiers,
        "policy": policy,
        "summary": summary,
    }
    return {
        "version": provisional["version"],
        "identity": {
            "algorithm": "sha256",
            "index": canonical_json_sha256(provisional),
        },
        "plan": provisional["plan"],
        "tiers": provisional["tiers"],
        "policy": provisional["policy"],
        "summary": provisional["summary"],
    }


def write_coverage_index(path: Path, report: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def verify_coverage_index(path: Path, root: Path = ROOT) -> dict:
    report, _ = _read_json(path, "coverage index")
    if set(report) != {
        "version",
        "identity",
        "plan",
        "tiers",
        "policy",
        "summary",
    }:
        raise ValidationError("coverage index has an unsupported schema")
    identity = report["identity"]
    if (
        report["version"] != PROTOCOL_VERSION
        or isinstance(report["version"], bool)
        or not isinstance(identity, dict)
        or set(identity) != {"algorithm", "index"}
        or identity["algorithm"] != "sha256"
    ):
        raise ValidationError("coverage index identity is malformed")
    provisional = dict(report)
    provisional.pop("identity")
    if identity["index"] != canonical_json_sha256(provisional):
        raise ValidationError("coverage index identity does not match its content")
    plan = report["plan"]
    if (
        not isinstance(plan, dict)
        or set(plan) != {"name", "sha256"}
        or not isinstance(plan["name"], str)
    ):
        raise ValidationError("coverage index plan identity is malformed")
    rebuilt = build_coverage_index(root / plan["name"], root)
    if rebuilt != report:
        raise ValidationError("coverage index disagrees with its current inputs")
    return report


def render_coverage_index(report: dict) -> list[str]:
    summary = report["summary"]
    lines = [
        "coverage index: "
        f"{summary['tierCount']} tiers, "
        f"{summary['uniqueCaseCount']} unique cases "
        f"({summary['tierCaseCount']} tier cases), "
        f"{summary['equalComparisonCount']}/{summary['comparisonCount']} "
        f"comparisons equal, findings {summary['findingCount']}"
    ]
    for tier in report["tiers"]:
        compared = sum(pair["comparedCases"] for pair in tier["pairs"])
        equal = sum(pair["equalCases"] for pair in tier["pairs"])
        machine = tier["machineCoverage"]
        machine_text = (
            ", no machine telemetry"
            if machine is None
            else (
                f", machine forms "
                f"{len(machine['forms']['executedObserved'])}, "
                f"steps {machine['steps']['interpreterStepCount']}"
            )
        )
        lines.append(
            f"coverage tier {tier['id']} ({tier['kind']}): "
            f"cases {tier['caseCount']}, comparisons {equal}/{compared} equal"
            f"{machine_text}"
        )
    machine = summary["machine"]
    lines.append(
        "coverage machine aggregate: "
        f"tiers {machine['coverageTierCount']}, cases {machine['caseCount']}, "
        f"forms {len(machine['forms']['executedObserved'])}, "
        f"administrative kinds "
        f"{len(machine['steps']['observedAdministrativeKinds'])}, "
        f"externals {len(machine['externals']['executedObserved'])}, "
        f"steps {machine['steps']['interpreterStepCount']}, "
        f"obligation failures {machine['obligationFailureCount']}, "
        f"telemetry failures {machine['telemetryFailureCount']}"
    )
    policy = report["policy"]
    lines.append(
        "coverage policy: "
        f"{'satisfied' if policy['satisfied'] else 'unsatisfied'}, "
        f"failures {policy['failureCount']}"
    )
    for tier in policy["tiers"]:
        lines.append(
            f"coverage policy tier {tier['id']}: "
            f"cases {tier['observedCases']}/{tier['minimumCases']} minimum, "
            f"comparisons {tier['observedComparisons']}/"
            f"{tier['minimumComparisons']} minimum, "
            f"backends {len(tier['observedBackends'])}/"
            f"{len(tier['requiredBackends'])} required, "
            f"machine {'present' if tier['machineCoveragePresent'] else 'absent'}, "
            f"failures {tier['failureCount']}"
        )
    aggregate_policy = policy["aggregate"]
    lines.append(
        "coverage policy aggregate: "
        f"unique cases {aggregate_policy['observedUniqueCases']}/"
        f"{aggregate_policy['minimumUniqueCases']} minimum, "
        f"tier cases {aggregate_policy['observedTierCases']}/"
        f"{aggregate_policy['minimumTierCases']} minimum, "
        f"comparisons {aggregate_policy['observedComparisons']}/"
        f"{aggregate_policy['minimumComparisons']} minimum, "
        f"failures {aggregate_policy['failureCount']}"
    )
    machine_policy = policy["machine"]
    missing_form_count = len(machine_policy["missingStaticForms"]) + len(
        machine_policy["missingExecutedForms"]
    )
    lines.append(
        "coverage policy machine: "
        f"cases {machine_policy['observedCases']}/"
        f"{machine_policy['minimumCases']} minimum, "
        f"steps {machine_policy['observedInterpreterSteps']}/"
        f"{machine_policy['minimumInterpreterSteps']} minimum, "
        f"missing forms {missing_form_count}, "
        f"administrative kinds "
        f"{len(machine_policy['missingAdministrativeKinds'])}, "
        f"externals {len(machine_policy['missingExternals'])}, "
        f"failures {machine_policy['failureCount']}"
    )
    return lines


def main() -> int:
    parser = argparse.ArgumentParser(
        description="compose verified validation coverage into semantic tiers"
    )
    parser.add_argument("--plan", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--verify-index", type=Path)
    args = parser.parse_args()
    if args.verify_index is not None:
        if args.plan is not None or args.out is not None:
            raise ValidationError(
                "--verify-index cannot be combined with --plan or --out"
            )
        report = verify_coverage_index(args.verify_index)
        print(f"verified validation coverage index {args.verify_index}")
    else:
        if args.plan is None or args.out is None:
            raise ValidationError("--plan and --out are required together")
        report = build_coverage_index(args.plan)
        write_coverage_index(args.out, report)
        print(f"wrote validation coverage index {args.out}")
    for line in render_coverage_index(report):
        print(line)
    return 0 if report["summary"]["complete"] else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validation coverage index error: {error}", file=sys.stderr)
        raise SystemExit(2)
