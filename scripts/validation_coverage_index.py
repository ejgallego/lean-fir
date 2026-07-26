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
    checked_sha256,
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


def _attributed_dimension(
    contributions: dict[str, list[str]],
    tier_order: list[str],
    required: list[str],
) -> dict:
    required_set = set(required)
    universe = {
        *required_set,
        *(
            item
            for tier_items in contributions.values()
            for item in tier_items
        ),
    }
    items = []
    for name in sorted(universe):
        contributing_tiers = [
            tier_id
            for tier_id in tier_order
            if name in contributions.get(tier_id, [])
        ]
        items.append(
            {
                "name": name,
                "tiers": contributing_tiers,
                "requiredByPolicy": name in required_set,
                "uniqueContribution": len(contributing_tiers) == 1,
            }
        )
    return {
        "items": items,
        "summary": {
            "itemCount": len(items),
            "observedItemCount": sum(int(bool(item["tiers"])) for item in items),
            "requiredItemCount": len(required_set),
            "coveredRequiredItemCount": sum(
                int(item["requiredByPolicy"] and bool(item["tiers"]))
                for item in items
            ),
            "uncoveredRequiredItemCount": sum(
                int(item["requiredByPolicy"] and not item["tiers"])
                for item in items
            ),
            "uniqueContributionItemCount": sum(
                int(item["uniqueContribution"]) for item in items
            ),
        },
    }


def coverage_attribution(tiers: list[dict], policy: dict) -> dict:
    """Attribute cases and machine observations to their contributing tiers."""
    tier_order = [tier["id"] for tier in tiers]
    case_contributions = {
        tier["id"]: list(tier["caseIds"]) for tier in tiers
    }
    static_form_contributions = {
        tier["id"]: (
            tier["machineCoverage"]["forms"]["staticObserved"]
            if tier["machineCoverage"] is not None
            else []
        )
        for tier in tiers
    }
    executed_form_contributions = {
        tier["id"]: (
            tier["machineCoverage"]["forms"]["executedObserved"]
            if tier["machineCoverage"] is not None
            else []
        )
        for tier in tiers
    }
    administrative_contributions = {
        tier["id"]: (
            [
                item["kind"]
                for item in tier["machineCoverage"]["steps"][
                    "observedAdministrativeKinds"
                ]
            ]
            if tier["machineCoverage"] is not None
            else []
        )
        for tier in tiers
    }
    external_contributions = {
        tier["id"]: (
            tier["machineCoverage"]["externals"]["executedObserved"]
            if tier["machineCoverage"] is not None
            else []
        )
        for tier in tiers
    }
    machine_policy = policy["machine"]
    dimensions = {
        "cases": _attributed_dimension(
            case_contributions, tier_order, []
        ),
        "staticForms": _attributed_dimension(
            static_form_contributions,
            tier_order,
            machine_policy["requiredStaticForms"],
        ),
        "executedForms": _attributed_dimension(
            executed_form_contributions,
            tier_order,
            machine_policy["requiredExecutedForms"],
        ),
        "administrativeKinds": _attributed_dimension(
            administrative_contributions,
            tier_order,
            machine_policy["requiredAdministrativeKinds"],
        ),
        "externals": _attributed_dimension(
            external_contributions,
            tier_order,
            machine_policy["requiredExternals"],
        ),
    }
    tier_reports = []
    contribution_maps = {
        "cases": case_contributions,
        "staticForms": static_form_contributions,
        "executedForms": executed_form_contributions,
        "administrativeKinds": administrative_contributions,
        "externals": external_contributions,
    }
    for tier in tiers:
        tier_id = tier["id"]
        tier_reports.append(
            {
                "id": tier_id,
                "machineCoveragePresent": (
                    tier["machineCoverage"] is not None
                ),
                "contributionCounts": {
                    name: len(contributions[tier_id])
                    for name, contributions in contribution_maps.items()
                },
                "uniqueContributions": {
                    name: [
                        item["name"]
                        for item in dimensions[name]["items"]
                        if item["tiers"] == [tier_id]
                    ]
                    for name in contribution_maps
                },
            }
        )
    uncovered = sum(
        dimension["summary"]["uncoveredRequiredItemCount"]
        for name, dimension in dimensions.items()
        if name != "cases"
    )
    unique = sum(
        dimension["summary"]["uniqueContributionItemCount"]
        for dimension in dimensions.values()
    )
    return {
        **dimensions,
        "tiers": tier_reports,
        "summary": {
            "machineCoverageTiers": [
                tier["id"]
                for tier in tiers
                if tier["machineCoverage"] is not None
            ],
            "uncoveredRequiredItemCount": uncovered,
            "uniqueContributionItemCount": unique,
            "complete": uncovered == 0,
        },
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


def _checked_snapshot_tiers(value: object) -> list[dict]:
    """Check retained tier claims before recomputing snapshot derivatives."""
    if not isinstance(value, list) or not value:
        raise ValidationError("coverage index snapshot tiers must be nonempty")
    checked: list[dict] = []
    tier_ids: list[str] = []
    for raw_tier in value:
        if not isinstance(raw_tier, dict) or set(raw_tier) != {
            "id",
            "kind",
            "matrix",
            "caseIds",
            "caseCount",
            "backends",
            "pairs",
            "providers",
            "consumers",
            "findingCount",
            "machineCoverageInput",
            "machineCoverage",
            "complete",
        }:
            raise ValidationError(
                "coverage index snapshot contains a malformed tier"
            )
        tier_id = validate_backend_name(
            raw_tier["id"], "coverage index snapshot tier id"
        )
        validate_backend_name(
            raw_tier["kind"], f"coverage index snapshot tier {tier_id} kind"
        )
        tier_ids.append(tier_id)

        matrix = raw_tier["matrix"]
        if (
            not isinstance(matrix, dict)
            or set(matrix) != {"name", "sha256", "run", "selection"}
            or not isinstance(matrix["name"], str)
            or not matrix["name"]
        ):
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} matrix is malformed"
            )
        checked_sha256(
            matrix["sha256"],
            f"coverage index snapshot tier {tier_id} matrix",
        )
        checked_sha256(
            matrix["run"],
            f"coverage index snapshot tier {tier_id} run identity",
        )
        checked_sha256(
            matrix["selection"],
            f"coverage index snapshot tier {tier_id} selection identity",
        )

        case_ids = _checked_string_list(
            raw_tier["caseIds"],
            f"coverage index snapshot tier {tier_id} caseIds",
        )
        case_count = _checked_nat(
            raw_tier["caseCount"],
            f"coverage index snapshot tier {tier_id} caseCount",
        )
        if case_count != len(case_ids):
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} case count disagrees "
                "with its retained case domain"
            )

        backends = raw_tier["backends"]
        if not isinstance(backends, list) or not backends:
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} backends must be nonempty"
            )
        backend_names: list[str] = []
        for backend in backends:
            if not isinstance(backend, dict) or set(backend) != {
                "backend",
                "selectedCaseCount",
                "resultCaseCount",
                "successfulCaseCount",
                "comparisonCount",
                "equalComparisonCount",
                "findingCount",
            }:
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} has malformed "
                    "backend coverage"
                )
            backend_name = validate_backend_name(
                backend["backend"],
                f"coverage index snapshot tier {tier_id} backend",
            )
            backend_names.append(backend_name)
            for field in (
                "selectedCaseCount",
                "resultCaseCount",
                "successfulCaseCount",
                "comparisonCount",
                "equalComparisonCount",
                "findingCount",
            ):
                _checked_nat(
                    backend[field],
                    f"coverage index snapshot tier {tier_id} backend "
                    f"{backend_name} {field}",
                )
            if backend["selectedCaseCount"] != case_count:
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} backend "
                    f"{backend_name} has the wrong selected case count"
                )
        if len(set(backend_names)) != len(backend_names):
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} repeats a backend"
            )

        pairs = raw_tier["pairs"]
        if not isinstance(pairs, list) or not pairs:
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} pairs must be nonempty"
            )
        pair_names: list[tuple[str, str]] = []
        for pair in pairs:
            if not isinstance(pair, dict) or set(pair) != {
                "reference",
                "candidate",
                "artifact",
                "sha256",
                "comparedCases",
                "equalCases",
                "findingCount",
            }:
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} has a malformed pair"
                )
            reference = validate_backend_name(
                pair["reference"],
                f"coverage index snapshot tier {tier_id} pair reference",
            )
            candidate = validate_backend_name(
                pair["candidate"],
                f"coverage index snapshot tier {tier_id} pair candidate",
            )
            if reference == candidate:
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} has a self-pair"
                )
            if (
                reference not in backend_names
                or candidate not in backend_names
                or not isinstance(pair["artifact"], str)
                or not pair["artifact"]
            ):
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} pair binding "
                    "is malformed"
                )
            checked_sha256(
                pair["sha256"],
                f"coverage index snapshot tier {tier_id} pair evidence",
            )
            for field in ("comparedCases", "equalCases", "findingCount"):
                _checked_nat(
                    pair[field],
                    f"coverage index snapshot tier {tier_id} pair {field}",
                )
            pair_names.append((reference, candidate))
        if len(set(pair_names)) != len(pair_names):
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} repeats a pair"
            )

        for field in ("providers", "consumers"):
            items = raw_tier[field]
            if not isinstance(items, list) or not all(
                isinstance(item, dict) for item in items
            ):
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} {field} "
                    "must be an array of objects"
                )

        finding_count = _checked_nat(
            raw_tier["findingCount"],
            f"coverage index snapshot tier {tier_id} findingCount",
        )
        machine_input = raw_tier["machineCoverageInput"]
        machine = raw_tier["machineCoverage"]
        if (machine_input is None) != (machine is None):
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} machine input "
                "and coverage disagree"
            )
        if machine_input is not None:
            if (
                not isinstance(machine_input, dict)
                or set(machine_input) != {"name", "sha256"}
                or not isinstance(machine_input["name"], str)
                or not machine_input["name"]
            ):
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} machine input "
                    "is malformed"
                )
            checked_sha256(
                machine_input["sha256"],
                f"coverage index snapshot tier {tier_id} machine input",
            )
            if not isinstance(machine, dict):
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} machine coverage "
                    "is malformed"
                )
            if _checked_nat(
                machine.get("caseCount"),
                f"coverage index snapshot tier {tier_id} machine caseCount",
            ) != case_count:
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} machine case "
                    "domain has the wrong size"
                )
            if not isinstance(machine.get("complete"), bool):
                raise ValidationError(
                    f"coverage index snapshot tier {tier_id} machine "
                    "completion is malformed"
                )

        complete = raw_tier["complete"]
        if not isinstance(complete, bool):
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} completion is malformed"
            )
        semantic_complete = (
            finding_count == 0
            and all(
                backend["resultCaseCount"] == case_count
                and backend["successfulCaseCount"] == case_count
                and backend["findingCount"] == 0
                for backend in backends
            )
            and all(
                pair["comparedCases"] == case_count
                and pair["equalCases"] == case_count
                and pair["findingCount"] == 0
                for pair in pairs
            )
        )
        expected_complete = semantic_complete and (
            machine is None or machine["complete"]
        )
        if complete != expected_complete:
            raise ValidationError(
                f"coverage index snapshot tier {tier_id} completion "
                "disagrees with its retained claims"
            )
        checked.append(raw_tier)
    if len(set(tier_ids)) != len(tier_ids):
        raise ValidationError("coverage index snapshot repeats a tier id")
    return checked


def coverage_policy_declaration(report: object) -> dict:
    """Recover the monotone policy declaration from its evaluated report."""
    if not isinstance(report, dict) or set(report) != {
        "tiers",
        "aggregate",
        "machine",
        "failureCount",
        "satisfied",
    }:
        raise ValidationError("coverage index snapshot policy is malformed")
    tier_reports = report["tiers"]
    if not isinstance(tier_reports, list):
        raise ValidationError("coverage index snapshot tier policy is malformed")
    tier_keys = {
        "id",
        "minimumCases",
        "observedCases",
        "caseDeficit",
        "minimumComparisons",
        "observedComparisons",
        "comparisonDeficit",
        "requiredBackends",
        "observedBackends",
        "missingBackends",
        "requireMachineCoverage",
        "machineCoveragePresent",
        "failureCount",
        "satisfied",
    }
    if any(
        not isinstance(item, dict) or set(item) != tier_keys
        for item in tier_reports
    ):
        raise ValidationError("coverage index snapshot tier policy is malformed")
    aggregate = report["aggregate"]
    aggregate_keys = {
        "minimumUniqueCases",
        "observedUniqueCases",
        "uniqueCaseDeficit",
        "minimumTierCases",
        "observedTierCases",
        "tierCaseDeficit",
        "minimumComparisons",
        "observedComparisons",
        "comparisonDeficit",
        "failureCount",
        "satisfied",
    }
    if not isinstance(aggregate, dict) or set(aggregate) != aggregate_keys:
        raise ValidationError(
            "coverage index snapshot aggregate policy is malformed"
        )
    machine = report["machine"]
    machine_keys = {
        "minimumCases",
        "observedCases",
        "caseDeficit",
        "minimumInterpreterSteps",
        "observedInterpreterSteps",
        "interpreterStepDeficit",
        "requiredStaticForms",
        "observedStaticForms",
        "missingStaticForms",
        "requiredExecutedForms",
        "observedExecutedForms",
        "missingExecutedForms",
        "requiredAdministrativeKinds",
        "observedAdministrativeKinds",
        "missingAdministrativeKinds",
        "requiredExternals",
        "observedExternals",
        "missingExternals",
        "failureCount",
        "satisfied",
    }
    if not isinstance(machine, dict) or set(machine) != machine_keys:
        raise ValidationError("coverage index snapshot machine policy is malformed")
    return {
        "tiers": [
            {
                "id": item["id"],
                "minimumCases": item["minimumCases"],
                "minimumComparisons": item["minimumComparisons"],
                "requiredBackends": item["requiredBackends"],
                "requireMachineCoverage": item["requireMachineCoverage"],
            }
            for item in tier_reports
        ],
        "aggregate": {
            "minimumUniqueCases": aggregate["minimumUniqueCases"],
            "minimumTierCases": aggregate["minimumTierCases"],
            "minimumComparisons": aggregate["minimumComparisons"],
        },
        "machine": {
            "minimumCases": machine["minimumCases"],
            "minimumInterpreterSteps": machine["minimumInterpreterSteps"],
            "requiredStaticForms": machine["requiredStaticForms"],
            "requiredExecutedForms": machine["requiredExecutedForms"],
            "requiredAdministrativeKinds": machine[
                "requiredAdministrativeKinds"
            ],
            "requiredExternals": machine["requiredExternals"],
        },
    }


def _coverage_index_from_components(
    plan: dict,
    tiers: list[dict],
    raw_policy: object,
) -> dict:
    """Derive the complete content-addressed index from retained components."""
    case_domains = [set(tier["caseIds"]) for tier in tiers]
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
    policy = coverage_policy_report(raw_policy, tiers, summary)
    attribution = coverage_attribution(tiers, policy)
    summary["policyFailureCount"] = policy["failureCount"]
    summary["attributionUncoveredRequiredItemCount"] = attribution["summary"][
        "uncoveredRequiredItemCount"
    ]
    summary["complete"] = (
        all(tier["complete"] for tier in tiers)
        and machine["complete"]
        and policy["satisfied"]
        and attribution["summary"]["complete"]
    )
    provisional = {
        "version": PROTOCOL_VERSION,
        "plan": plan,
        "tiers": tiers,
        "policy": policy,
        "attribution": attribution,
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
        "attribution": provisional["attribution"],
        "summary": provisional["summary"],
    }


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
    for raw_tier in raw_tiers:
        tier, _ = _tier_from_config(raw_tier, plan_path, root)
        tiers.append(tier)
    tier_ids = [tier["id"] for tier in tiers]
    if len(set(tier_ids)) != len(tier_ids):
        raise ValidationError("coverage index plan repeats a tier id")
    return _coverage_index_from_components(
        {
            "name": plan_name,
            "sha256": sha256_bytes(plan_content),
        },
        tiers,
        plan["policy"],
    )


def write_coverage_index(path: Path, report: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def verify_coverage_index_snapshot(path: Path) -> dict:
    """Verify a relocatable index snapshot from its retained claims alone."""
    report, _ = _read_json(path, "coverage index")
    if set(report) != {
        "version",
        "identity",
        "plan",
        "tiers",
        "policy",
        "attribution",
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
    checked_sha256(identity["index"], "coverage index identity")
    provisional = dict(report)
    provisional.pop("identity")
    if identity["index"] != canonical_json_sha256(provisional):
        raise ValidationError("coverage index identity does not match its content")
    plan = report["plan"]
    if (
        not isinstance(plan, dict)
        or set(plan) != {"name", "sha256"}
        or not isinstance(plan["name"], str)
        or not plan["name"]
        or Path(plan["name"]).is_absolute()
        or ".." in Path(plan["name"]).parts
    ):
        raise ValidationError("coverage index plan identity is malformed")
    checked_sha256(plan["sha256"], "coverage index plan identity")
    tiers = _checked_snapshot_tiers(report["tiers"])
    raw_policy = coverage_policy_declaration(report["policy"])
    try:
        rebuilt = _coverage_index_from_components(plan, tiers, raw_policy)
    except ValidationError:
        raise
    except (KeyError, TypeError, ValueError) as error:
        raise ValidationError(
            "coverage index snapshot retained claims are malformed"
        ) from error
    if rebuilt != report:
        raise ValidationError(
            "coverage index snapshot derivatives disagree with retained claims"
        )
    return report


def verify_coverage_index(path: Path, root: Path = ROOT) -> dict:
    """Verify a snapshot and then rederive it from all current source inputs."""
    report = verify_coverage_index_snapshot(path)
    plan = report["plan"]
    rebuilt = build_coverage_index(root / plan["name"], root)
    if rebuilt != report:
        raise ValidationError("coverage index disagrees with its current inputs")
    return report


def _attribution_dimension_delta(before: dict, after: dict) -> dict:
    before_items = {
        item["name"]: item for item in before["items"]
    }
    after_items = {
        item["name"]: item for item in after["items"]
    }
    before_observed = {
        name for name, item in before_items.items() if item["tiers"]
    }
    after_observed = {
        name for name, item in after_items.items() if item["tiers"]
    }
    before_required = {
        name
        for name, item in before_items.items()
        if item["requiredByPolicy"]
    }
    after_required = {
        name
        for name, item in after_items.items()
        if item["requiredByPolicy"]
    }
    before_uncovered_required = before_required - before_observed
    after_uncovered_required = after_required - after_observed
    attribution_changed = []
    for name in sorted(before_observed & after_observed):
        before_tiers = before_items[name]["tiers"]
        after_tiers = after_items[name]["tiers"]
        if before_tiers != after_tiers:
            attribution_changed.append(
                {
                    "name": name,
                    "beforeTiers": before_tiers,
                    "afterTiers": after_tiers,
                    "addedTiers": sorted(
                        set(after_tiers) - set(before_tiers)
                    ),
                    "removedTiers": sorted(
                        set(before_tiers) - set(after_tiers)
                    ),
                }
            )
    return {
        "added": sorted(after_observed - before_observed),
        "removed": sorted(before_observed - after_observed),
        "policyAdded": sorted(after_required - before_required),
        "policyRemoved": sorted(before_required - after_required),
        "newlyCoveredRequired": sorted(
            (
                before_uncovered_required - after_uncovered_required
            )
            & after_required
            & after_observed
        ),
        "newlyUncoveredRequired": sorted(
            after_uncovered_required - before_uncovered_required
        ),
        "attributionChanged": attribution_changed,
    }


def _tier_comparison(before: dict, after: dict) -> dict:
    before_cases = set(before["caseIds"])
    after_cases = set(after["caseIds"])
    before_backends = {
        item["backend"] for item in before["backends"]
    }
    after_backends = {
        item["backend"] for item in after["backends"]
    }
    before_pairs = {
        (item["reference"], item["candidate"]) for item in before["pairs"]
    }
    after_pairs = {
        (item["reference"], item["candidate"]) for item in after["pairs"]
    }

    def rendered_pairs(pairs: set[tuple[str, str]]) -> list[dict]:
        return [
            {"reference": reference, "candidate": candidate}
            for reference, candidate in sorted(pairs)
        ]

    before_comparisons = sum(
        item["comparedCases"] for item in before["pairs"]
    )
    after_comparisons = sum(
        item["comparedCases"] for item in after["pairs"]
    )
    return {
        "id": before["id"],
        "retainedClaimsChanged": before != after,
        "kind": {
            "before": before["kind"],
            "after": after["kind"],
            "changed": before["kind"] != after["kind"],
        },
        "cases": {
            "before": before["caseCount"],
            "after": after["caseCount"],
            "delta": after["caseCount"] - before["caseCount"],
            "added": sorted(after_cases - before_cases),
            "removed": sorted(before_cases - after_cases),
        },
        "comparisons": {
            "before": before_comparisons,
            "after": after_comparisons,
            "delta": after_comparisons - before_comparisons,
        },
        "backends": {
            "added": sorted(after_backends - before_backends),
            "removed": sorted(before_backends - after_backends),
        },
        "pairs": {
            "added": rendered_pairs(after_pairs - before_pairs),
            "removed": rendered_pairs(before_pairs - after_pairs),
        },
        "matrixChanged": before["matrix"] != after["matrix"],
        "providerCoverageChanged": (
            before["providers"] != after["providers"]
            or before["consumers"] != after["consumers"]
        ),
        "machineCoverageChanged": (
            before["machineCoverageInput"]
            != after["machineCoverageInput"]
            or before["machineCoverage"] != after["machineCoverage"]
        ),
        "findings": {
            "before": before["findingCount"],
            "after": after["findingCount"],
            "delta": after["findingCount"] - before["findingCount"],
        },
        "complete": {
            "before": before["complete"],
            "after": after["complete"],
            "changed": before["complete"] != after["complete"],
        },
    }


def coverage_policy_slack(policy: dict) -> dict:
    """Expose signed distance from every numeric and set-valued policy floor."""
    return {
        "tiers": [
            {
                "id": tier["id"],
                "cases": tier["observedCases"] - tier["minimumCases"],
                "comparisons": (
                    tier["observedComparisons"]
                    - tier["minimumComparisons"]
                ),
                "requiredBackends": -len(tier["missingBackends"]),
                "machineCoverage": (
                    -1
                    if tier["requireMachineCoverage"]
                    and not tier["machineCoveragePresent"]
                    else 0
                ),
            }
            for tier in policy["tiers"]
        ],
        "aggregate": {
            "uniqueCases": (
                policy["aggregate"]["observedUniqueCases"]
                - policy["aggregate"]["minimumUniqueCases"]
            ),
            "tierCases": (
                policy["aggregate"]["observedTierCases"]
                - policy["aggregate"]["minimumTierCases"]
            ),
            "comparisons": (
                policy["aggregate"]["observedComparisons"]
                - policy["aggregate"]["minimumComparisons"]
            ),
        },
        "machine": {
            "cases": (
                policy["machine"]["observedCases"]
                - policy["machine"]["minimumCases"]
            ),
            "interpreterSteps": (
                policy["machine"]["observedInterpreterSteps"]
                - policy["machine"]["minimumInterpreterSteps"]
            ),
            "staticForms": -len(policy["machine"]["missingStaticForms"]),
            "executedForms": -len(
                policy["machine"]["missingExecutedForms"]
            ),
            "administrativeKinds": -len(
                policy["machine"]["missingAdministrativeKinds"]
            ),
            "externals": -len(policy["machine"]["missingExternals"]),
        },
    }


def _slack_field_delta(before: int | None, after: int | None) -> dict:
    return {
        "before": before,
        "after": after,
        "delta": (
            None if before is None or after is None else after - before
        ),
    }


def _policy_slack_comparison(before: dict, after: dict) -> dict:
    before_tiers = {item["id"]: item for item in before["tiers"]}
    after_tiers = {item["id"]: item for item in after["tiers"]}
    tier_fields = (
        "cases",
        "comparisons",
        "requiredBackends",
        "machineCoverage",
    )
    tiers = []
    comparable_deltas: list[int] = []
    for tier_id in sorted(before_tiers.keys() | after_tiers.keys()):
        before_tier = before_tiers.get(tier_id)
        after_tier = after_tiers.get(tier_id)
        fields = {
            field: _slack_field_delta(
                None if before_tier is None else before_tier[field],
                None if after_tier is None else after_tier[field],
            )
            for field in tier_fields
        }
        comparable_deltas.extend(
            item["delta"]
            for item in fields.values()
            if item["delta"] is not None
        )
        tiers.append({"id": tier_id, **fields})

    def compared_group(
        before_group: dict, after_group: dict
    ) -> dict:
        result = {
            field: _slack_field_delta(
                before_group[field], after_group[field]
            )
            for field in before_group
        }
        comparable_deltas.extend(item["delta"] for item in result.values())
        return result

    return {
        "before": before,
        "after": after,
        "tiers": tiers,
        "aggregate": compared_group(
            before["aggregate"], after["aggregate"]
        ),
        "machine": compared_group(before["machine"], after["machine"]),
        "increaseCount": sum(delta > 0 for delta in comparable_deltas),
        "decreaseCount": sum(delta < 0 for delta in comparable_deltas),
    }


def compare_coverage_indexes(before: dict, after: dict) -> dict:
    """Classify changes between two independently verified index snapshots."""
    before_tiers = {tier["id"]: tier for tier in before["tiers"]}
    after_tiers = {tier["id"]: tier for tier in after["tiers"]}
    added_tiers = sorted(after_tiers.keys() - before_tiers.keys())
    removed_tiers = sorted(before_tiers.keys() - after_tiers.keys())
    changed_tiers = [
        _tier_comparison(before_tiers[tier_id], after_tiers[tier_id])
        for tier_id in sorted(before_tiers.keys() & after_tiers.keys())
        if before_tiers[tier_id] != after_tiers[tier_id]
    ]
    dimension_names = (
        "cases",
        "staticForms",
        "executedForms",
        "administrativeKinds",
        "externals",
    )
    dimensions = {
        name: _attribution_dimension_delta(
            before["attribution"][name],
            after["attribution"][name],
        )
        for name in dimension_names
    }
    observed_added = sum(
        len(dimension["added"]) for dimension in dimensions.values()
    )
    observed_removed = sum(
        len(dimension["removed"]) for dimension in dimensions.values()
    )
    attribution_gains = sum(
        len(change["addedTiers"])
        for dimension in dimensions.values()
        for change in dimension["attributionChanged"]
    )
    attribution_losses = sum(
        len(change["removedTiers"])
        for dimension in dimensions.values()
        for change in dimension["attributionChanged"]
    )
    attribution_changes = sum(
        len(dimension["attributionChanged"])
        for dimension in dimensions.values()
    )
    newly_covered = sum(
        len(dimension["newlyCoveredRequired"])
        for dimension in dimensions.values()
    )
    newly_uncovered = sum(
        len(dimension["newlyUncoveredRequired"])
        for dimension in dimensions.values()
    )
    before_slack = coverage_policy_slack(before["policy"])
    after_slack = coverage_policy_slack(after["policy"])
    slack = _policy_slack_comparison(before_slack, after_slack)
    failure_delta = (
        after["policy"]["failureCount"]
        - before["policy"]["failureCount"]
    )
    requirements_changed = (
        coverage_policy_declaration(before["policy"])
        != coverage_policy_declaration(after["policy"])
    )
    coverage_regressed = bool(
        removed_tiers
        or observed_removed
        or attribution_losses
        or newly_uncovered
    )
    coverage_gained = bool(
        added_tiers
        or observed_added
        or attribution_gains
        or newly_covered
    )
    regression_signals = (
        len(removed_tiers)
        + observed_removed
        + attribution_losses
        + newly_uncovered
        + slack["decreaseCount"]
        + max(0, failure_delta)
    )
    gain_signals = (
        len(added_tiers)
        + observed_added
        + attribution_gains
        + newly_covered
        + slack["increaseCount"]
        + max(0, -failure_delta)
    )
    return {
        "version": PROTOCOL_VERSION,
        "before": {
            "index": before["identity"]["index"],
            "plan": before["plan"]["sha256"],
        },
        "after": {
            "index": after["identity"]["index"],
            "plan": after["plan"]["sha256"],
        },
        "classification": {
            "indexChanged": (
                before["identity"]["index"] != after["identity"]["index"]
            ),
            "planChanged": (
                before["plan"]["sha256"] != after["plan"]["sha256"]
            ),
            "tierClaimsChanged": bool(
                added_tiers or removed_tiers or changed_tiers
            ),
            "coverageGained": coverage_gained,
            "coverageRegressed": coverage_regressed,
            "attributionChanged": attribution_changes > 0,
            "policyRequirementsChanged": requirements_changed,
            "policySatisfactionChanged": (
                before["policy"]["satisfied"]
                != after["policy"]["satisfied"]
            ),
            "policyFailuresIncreased": failure_delta > 0,
            "policySlackRegressed": slack["decreaseCount"] > 0,
            "regressionDetected": regression_signals > 0,
        },
        "summary": {
            "tierAddedCount": len(added_tiers),
            "tierRemovedCount": len(removed_tiers),
            "tierChangedCount": len(changed_tiers),
            "observedItemAddedCount": observed_added,
            "observedItemRemovedCount": observed_removed,
            "attributionChangeCount": attribution_changes,
            "attributionTierGainCount": attribution_gains,
            "attributionTierLossCount": attribution_losses,
            "newlyCoveredRequiredItemCount": newly_covered,
            "newlyUncoveredRequiredItemCount": newly_uncovered,
            "policyFailureCountBefore": before["policy"]["failureCount"],
            "policyFailureCountAfter": after["policy"]["failureCount"],
            "policyFailureCountDelta": failure_delta,
            "policySlackIncreaseCount": slack["increaseCount"],
            "policySlackDecreaseCount": slack["decreaseCount"],
            "gainSignalCount": gain_signals,
            "regressionSignalCount": regression_signals,
        },
        "tiers": {
            "added": added_tiers,
            "removed": removed_tiers,
            "changed": changed_tiers,
        },
        "coverage": dimensions,
        "policy": {
            "beforeSatisfied": before["policy"]["satisfied"],
            "afterSatisfied": after["policy"]["satisfied"],
            "requirementsChanged": requirements_changed,
            "slack": slack,
        },
    }


def compare_verified_coverage_indexes(
    before_path: Path,
    after_path: Path,
) -> dict:
    """Verify two relocatable snapshots and compare their retained claims."""
    return compare_coverage_indexes(
        verify_coverage_index_snapshot(before_path),
        verify_coverage_index_snapshot(after_path),
    )


def render_coverage_index_comparison(comparison: dict) -> list[str]:
    """Render a concise stable report from a coverage-index comparison."""
    before = comparison["before"]
    after = comparison["after"]
    classification = comparison["classification"]
    summary = comparison["summary"]

    def state(field: str) -> str:
        return "yes" if classification[field] else "no"

    lines = [
        f"coverage index comparison: {before['index']} -> {after['index']}",
        "classification: "
        f"tiers changed {state('tierClaimsChanged')}, "
        f"coverage gained {state('coverageGained')}, "
        f"coverage regressed {state('coverageRegressed')}, "
        f"policy slack regressed {state('policySlackRegressed')}, "
        f"regression detected {state('regressionDetected')}",
        "tiers: "
        f"+{summary['tierAddedCount']} "
        f"-{summary['tierRemovedCount']} "
        f"~{summary['tierChangedCount']}",
        "coverage inventory: "
        f"+{summary['observedItemAddedCount']} "
        f"-{summary['observedItemRemovedCount']}, "
        f"attribution ~{summary['attributionChangeCount']} "
        f"(tier +{summary['attributionTierGainCount']} "
        f"-{summary['attributionTierLossCount']}), "
        f"required covered +{summary['newlyCoveredRequiredItemCount']} "
        f"-{summary['newlyUncoveredRequiredItemCount']}",
        "policy: "
        f"satisfied {comparison['policy']['beforeSatisfied']} -> "
        f"{comparison['policy']['afterSatisfied']}, "
        f"failures {summary['policyFailureCountBefore']} -> "
        f"{summary['policyFailureCountAfter']}, "
        f"slack fields +{summary['policySlackIncreaseCount']} "
        f"-{summary['policySlackDecreaseCount']}",
    ]
    for tier in comparison["tiers"]["changed"]:
        lines.append(
            f"tier {tier['id']}: "
            f"cases {tier['cases']['before']} -> {tier['cases']['after']}, "
            f"comparisons {tier['comparisons']['before']} -> "
            f"{tier['comparisons']['after']}, "
            f"findings {tier['findings']['before']} -> "
            f"{tier['findings']['after']}"
        )
    for name, dimension in comparison["coverage"].items():
        if (
            dimension["added"]
            or dimension["removed"]
            or dimension["attributionChanged"]
            or dimension["newlyCoveredRequired"]
            or dimension["newlyUncoveredRequired"]
        ):
            lines.append(
                f"{name}: +{len(dimension['added'])} "
                f"-{len(dimension['removed'])} "
                f"attribution ~{len(dimension['attributionChanged'])}, "
                f"required covered "
                f"+{len(dimension['newlyCoveredRequired'])} "
                f"-{len(dimension['newlyUncoveredRequired'])}"
            )
    return lines


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
    attribution = report["attribution"]
    lines.append(
        "coverage attribution: "
        f"cases {attribution['cases']['summary']['observedItemCount']}, "
        f"static forms "
        f"{attribution['staticForms']['summary']['observedItemCount']}, "
        f"executed forms "
        f"{attribution['executedForms']['summary']['observedItemCount']}, "
        f"administrative kinds "
        f"{attribution['administrativeKinds']['summary']['observedItemCount']}, "
        f"externals {attribution['externals']['summary']['observedItemCount']}, "
        f"unique contributions "
        f"{attribution['summary']['uniqueContributionItemCount']}, "
        f"uncovered required "
        f"{attribution['summary']['uncoveredRequiredItemCount']}"
    )
    for tier in attribution["tiers"]:
        unique = tier["uniqueContributions"]
        unique_administrative = (
            ",".join(unique["administrativeKinds"])
            if unique["administrativeKinds"]
            else "none"
        )
        lines.append(
            f"coverage attribution tier {tier['id']}: "
            f"unique cases {len(unique['cases'])}, "
            f"static forms {len(unique['staticForms'])}, "
            f"executed forms {len(unique['executedForms'])}, "
            f"administrative {unique_administrative}, "
            f"externals {len(unique['externals'])}"
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
    parser.add_argument(
        "--compare-index",
        nargs=2,
        type=Path,
        metavar=("BEFORE", "AFTER"),
        help="structurally verify and compare two relocatable index snapshots",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit --compare-index as stable JSON",
    )
    args = parser.parse_args()
    inspection_modes = sum(
        int(option is not None)
        for option in (args.verify_index, args.compare_index)
    )
    if inspection_modes:
        if (
            inspection_modes != 1
            or args.plan is not None
            or args.out is not None
            or (args.json and args.compare_index is None)
        ):
            raise ValidationError(
                "index inspection options are mutually exclusive and cannot "
                "be combined with index creation options"
            )
        if args.compare_index is not None:
            before_path, after_path = args.compare_index
            comparison = compare_verified_coverage_indexes(
                before_path, after_path
            )
            if args.json:
                print(json.dumps(comparison, indent=2, sort_keys=True))
            else:
                for line in render_coverage_index_comparison(comparison):
                    print(line)
            return 0
        report = verify_coverage_index(args.verify_index)
        print(f"verified validation coverage index {args.verify_index}")
    else:
        if args.json:
            raise ValidationError("--json requires --compare-index")
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
