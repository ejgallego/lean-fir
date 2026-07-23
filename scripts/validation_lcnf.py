#!/usr/bin/env python3
"""LCNF-specific execution and coverage policy for interpreter validation."""

from __future__ import annotations

import json
import sys
from pathlib import Path

from validation_harness import (
    PROTOCOL_VERSION,
    BackendAudit,
    BackendRun,
    BuildContext,
    RunContext,
    ValidationError,
    ValidationFinding,
    ValidationTool,
    records_from_output,
    resolve_lake_command,
    result_map,
    run,
    validation_tool_from_file,
    write_process_artifacts,
)


LCNF_MANIFEST_FIELDS = {
    "requiredLcnfForms",
    "requiredExecutedLcnfForms",
    "requiredExecutedLcnfFormCounts",
    "requiredExternals",
    "requiredExecutedExternals",
    "requiredExecutedExternalCounts",
}


def prepare_manifest(descriptors: list[dict]) -> list[dict]:
    """Validate and canonicalize the LCNF-owned manifest extension."""
    prepared: list[dict] = []
    for descriptor in descriptors:
        case_id = descriptor["id"]
        missing = sorted(LCNF_MANIFEST_FIELDS - descriptor.keys())
        if missing:
            raise ValidationError(
                f"native corpus manifest/{case_id}: missing {', '.join(missing)}"
            )

        def checked_names(field_name: str) -> list[str]:
            values = descriptor[field_name]
            if not isinstance(values, list) or not all(
                isinstance(value, str) and value for value in values
            ):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: malformed {field_name}"
                )
            if len(set(values)) != len(values):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: duplicate {field_name}"
                )
            return sorted(values)

        def checked_count_requirements(
            field_name: str,
            name_key: str,
            static_required_names: list[str],
            executed_required_names: list[str],
        ) -> list[dict]:
            requirements = descriptor[field_name]
            if not isinstance(requirements, list):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: malformed {field_name}"
                )
            prepared_requirements: list[dict] = []
            counted_names: set[str] = set()
            for requirement in requirements:
                if (
                    not isinstance(requirement, dict)
                    or set(requirement) != {name_key, "minimum", "maximum"}
                    or not isinstance(requirement[name_key], str)
                    or not requirement[name_key]
                    or not isinstance(requirement["minimum"], int)
                    or isinstance(requirement["minimum"], bool)
                    or requirement["minimum"] < 0
                    or (
                        requirement["maximum"] is not None
                        and (
                            not isinstance(requirement["maximum"], int)
                            or isinstance(requirement["maximum"], bool)
                            or requirement["maximum"] < requirement["minimum"]
                        )
                    )
                    or (
                        requirement["minimum"] == 0
                        and requirement["maximum"] != 0
                    )
                ):
                    raise ValidationError(
                        f"native corpus manifest/{case_id}: malformed {field_name}"
                    )
                name = requirement[name_key]
                if name in counted_names:
                    raise ValidationError(
                        f"native corpus manifest/{case_id}: duplicate {field_name}"
                    )
                counted_names.add(name)
                prepared_requirements.append(
                    {
                        name_key: name,
                        "minimum": requirement["minimum"],
                        "maximum": requirement["maximum"],
                    }
                )
            positive_names = {
                requirement[name_key]
                for requirement in prepared_requirements
                if requirement["minimum"] > 0
            }
            zero_names = counted_names - positive_names
            kind = "LCNF forms" if name_key == "form" else "externals"
            if not positive_names <= set(executed_required_names):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: counted executed "
                    f"{kind} "
                    "must also be required"
                )
            if not zero_names <= set(static_required_names):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: zero-counted {kind} "
                    "must also be statically required"
                )
            if zero_names & set(executed_required_names):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: zero-counted {kind} "
                    "cannot also be required executed"
                )
            return sorted(
                prepared_requirements,
                key=lambda requirement: requirement[name_key],
            )

        required_forms = checked_names("requiredLcnfForms")
        required_executed_forms = checked_names("requiredExecutedLcnfForms")
        prepared_count_requirements = checked_count_requirements(
            "requiredExecutedLcnfFormCounts",
            "form",
            required_forms,
            required_executed_forms,
        )

        required_externals = checked_names("requiredExternals")
        required_executed_externals = checked_names("requiredExecutedExternals")
        prepared_external_count_requirements = checked_count_requirements(
            "requiredExecutedExternalCounts",
            "external",
            required_externals,
            required_executed_externals,
        )

        effect_externals = {
            projection["external"] for projection in descriptor["effectProjections"]
        }
        if not effect_externals <= (
            set(required_externals) & set(required_executed_externals)
        ):
            raise ValidationError(
                f"native corpus manifest/{case_id}: effect projection externals "
                "must be required and executed"
            )

        item = dict(descriptor)
        item["requiredLcnfForms"] = required_forms
        item["requiredExecutedLcnfForms"] = required_executed_forms
        item["requiredExecutedLcnfFormCounts"] = prepared_count_requirements
        item["requiredExternals"] = required_externals
        item["requiredExecutedExternals"] = required_executed_externals
        item["requiredExecutedExternalCounts"] = (
            prepared_external_count_requirements
        )
        prepared.append(item)
    return prepared


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
    """Return whether a comma-separated form diagnostic exists and its set."""
    if record is None:
        return False, []
    values = diagnostics(record)
    if key not in values:
        return False, []
    forms = [form.strip() for form in values[key].split(",") if form.strip()]
    return True, sorted(set(forms))


def diagnostic_named_counts(
    record: dict | None, key: str, name_key: str
) -> tuple[bool, dict[str, int] | None]:
    """Return a JSON named-count diagnostic, preserving absence vs invalidity."""
    if record is None:
        return False, {}
    values = diagnostics(record)
    if key not in values:
        return False, {}
    try:
        items = json.loads(values[key])
    except (TypeError, json.JSONDecodeError):
        return True, None
    if not isinstance(items, list):
        return True, None
    counts: dict[str, int] = {}
    for item in items:
        if (
            not isinstance(item, dict)
            or set(item) != {name_key, "count"}
            or not isinstance(item[name_key], str)
            or not item[name_key]
            or not isinstance(item["count"], int)
            or isinstance(item["count"], bool)
            or item["count"] <= 0
            or item[name_key] in counts
        ):
            return True, None
        counts[item[name_key]] = item["count"]
    return True, dict(sorted(counts.items()))


def named_count_items(
    counts: dict[str, int], name_key: str, value_key: str
) -> list[dict]:
    return [
        {name_key: name, value_key: count}
        for name, count in sorted(counts.items())
    ]


def required_count_observations(
    requirements: list[dict], observed: dict[str, int], name_key: str
) -> list[dict]:
    """Project every required name to an explicit observed count, including zero."""
    return [
        {
            name_key: requirement[name_key],
            "count": observed.get(requirement[name_key], 0),
        }
        for requirement in requirements
    ]


def unsatisfied_count_requirements(
    requirements: list[dict], observed: dict[str, int], name_key: str
) -> list[dict]:
    """Return count requirements violated below or above their inclusive bounds."""
    unsatisfied: list[dict] = []
    for requirement in requirements:
        count = observed.get(requirement[name_key], 0)
        maximum = requirement["maximum"]
        if count < requirement["minimum"] or (
            maximum is not None and count > maximum
        ):
            unsatisfied.append({**requirement, "observed": count})
    return unsatisfied


def render_count_violations(items: list[dict], name_key: str) -> str:
    """Render deterministic below-minimum and above-maximum count failures."""
    rendered: list[str] = []
    for item in items:
        if item["observed"] < item["minimum"]:
            rendered.append(
                f"{item[name_key]}={item['observed']}<{item['minimum']}"
            )
        else:
            rendered.append(
                f"{item[name_key]}={item['observed']}>{item['maximum']}"
            )
    return ",".join(rendered)


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
) -> tuple[dict, list[ValidationFinding]]:
    """Build deterministic static and executed LCNF and external coverage."""
    descriptor_by_id = {descriptor["id"]: descriptor for descriptor in descriptors}
    cases: list[dict] = []
    findings: list[ValidationFinding] = []
    static_required: set[str] = set()
    static_observed: set[str] = set()
    executed_required: set[str] = set()
    executed_observed: set[str] = set()
    static_missing_count = 0
    executed_missing_count = 0
    executed_diagnostic_count = 0
    executed_requirement_count = 0
    executed_count_diagnostic_count = 0
    executed_count_valid_diagnostic_count = 0
    executed_count_requirement_count = 0
    executed_count_upper_bound_case_count = 0
    executed_count_zero_case_count = 0
    executed_count_zero_requirement_count = 0
    executed_count_missing_count = 0
    executed_count_required_totals: dict[str, int] = {}
    executed_count_bounded_maximum_totals: dict[str, int] = {}
    executed_count_observed_totals: dict[str, int] = {}
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
    executed_external_count_diagnostic_count = 0
    executed_external_count_valid_diagnostic_count = 0
    executed_external_count_requirement_count = 0
    executed_external_count_upper_bound_case_count = 0
    executed_external_count_zero_case_count = 0
    executed_external_count_zero_requirement_count = 0
    executed_external_count_missing_count = 0
    executed_external_count_required_totals: dict[str, int] = {}
    executed_external_count_bounded_maximum_totals: dict[str, int] = {}
    executed_external_count_observed_totals: dict[str, int] = {}
    interpreter_steps: list[int] = []

    for case_id in sorted(selected):
        descriptor = descriptor_by_id[case_id]
        record = results.get(case_id)
        static_present, observed_static = diagnostic_forms(record, "lcnf-forms")
        executed_present, observed_executed = diagnostic_forms(
            record, "executed-lcnf-forms"
        )
        executed_counts_present, observed_executed_counts = diagnostic_named_counts(
            record, "executed-lcnf-form-counts", "form"
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
        (
            executed_external_counts_present,
            observed_executed_external_counts,
        ) = diagnostic_named_counts(record, "executed-external-counts", "external")
        executed_external_missing_present, reported_missing_executed_externals = (
            diagnostic_forms(record, "missing-executed-externals")
        )
        required_static = descriptor["requiredLcnfForms"]
        required_executed = descriptor["requiredExecutedLcnfForms"]
        required_executed_counts = descriptor["requiredExecutedLcnfFormCounts"]
        required_static_externals = descriptor["requiredExternals"]
        required_executed_externals = descriptor["requiredExecutedExternals"]
        required_executed_external_counts = descriptor[
            "requiredExecutedExternalCounts"
        ]
        executed_obligations_active = bool(required_executed)
        executed_count_obligations_active = bool(required_executed_counts)
        executed_count_upper_bounds_active = any(
            requirement["maximum"] is not None
            for requirement in required_executed_counts
        )
        executed_count_zero_counts_active = any(
            requirement["minimum"] == 0
            for requirement in required_executed_counts
        )
        static_external_obligations_active = bool(required_static_externals)
        executed_external_obligations_active = bool(required_executed_externals)
        executed_external_count_obligations_active = bool(
            required_executed_external_counts
        )
        executed_external_count_upper_bounds_active = any(
            requirement["maximum"] is not None
            for requirement in required_executed_external_counts
        )
        executed_external_count_zero_counts_active = any(
            requirement["minimum"] == 0
            for requirement in required_executed_external_counts
        )
        missing_static = sorted(set(required_static) - set(observed_static))
        missing_executed = sorted(set(required_executed) - set(observed_executed))
        observed_count_map = observed_executed_counts or {}
        unsatisfied_executed_counts = unsatisfied_count_requirements(
            required_executed_counts, observed_count_map, "form"
        )
        missing_static_externals = sorted(
            set(required_static_externals) - set(observed_static_externals)
        )
        missing_executed_externals = sorted(
            set(required_executed_externals) - set(observed_executed_externals)
        )
        observed_external_count_map = observed_executed_external_counts or {}
        unsatisfied_executed_external_counts = unsatisfied_count_requirements(
            required_executed_external_counts,
            observed_external_count_map,
            "external",
        )

        static_required.update(required_static)
        static_observed.update(observed_static)
        executed_required.update(required_executed)
        executed_observed.update(observed_executed)
        static_missing_count += len(missing_static)
        executed_missing_count += len(missing_executed)
        executed_diagnostic_count += int(executed_present)
        executed_requirement_count += int(executed_obligations_active)
        executed_count_diagnostic_count += int(executed_counts_present)
        executed_count_valid_diagnostic_count += int(
            executed_counts_present and observed_executed_counts is not None
        )
        executed_count_requirement_count += int(executed_count_obligations_active)
        executed_count_upper_bound_case_count += int(
            executed_count_upper_bounds_active
        )
        executed_count_zero_case_count += int(executed_count_zero_counts_active)
        executed_count_zero_requirement_count += sum(
            requirement["minimum"] == 0
            for requirement in required_executed_counts
        )
        executed_count_missing_count += len(unsatisfied_executed_counts)
        for requirement in required_executed_counts:
            form = requirement["form"]
            executed_count_required_totals[form] = (
                executed_count_required_totals.get(form, 0)
                + requirement["minimum"]
            )
            if requirement["maximum"] is not None:
                executed_count_bounded_maximum_totals[form] = (
                    executed_count_bounded_maximum_totals.get(form, 0)
                    + requirement["maximum"]
                )
        if observed_executed_counts is not None:
            for form, count in observed_executed_counts.items():
                executed_count_observed_totals[form] = (
                    executed_count_observed_totals.get(form, 0) + count
                )
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
        executed_external_count_diagnostic_count += int(
            executed_external_counts_present
        )
        executed_external_count_valid_diagnostic_count += int(
            executed_external_counts_present
            and observed_executed_external_counts is not None
        )
        executed_external_count_requirement_count += int(
            executed_external_count_obligations_active
        )
        executed_external_count_upper_bound_case_count += int(
            executed_external_count_upper_bounds_active
        )
        executed_external_count_zero_case_count += int(
            executed_external_count_zero_counts_active
        )
        executed_external_count_zero_requirement_count += sum(
            requirement["minimum"] == 0
            for requirement in required_executed_external_counts
        )
        executed_external_count_missing_count += len(
            unsatisfied_executed_external_counts
        )
        for requirement in required_executed_external_counts:
            external = requirement["external"]
            executed_external_count_required_totals[external] = (
                executed_external_count_required_totals.get(external, 0)
                + requirement["minimum"]
            )
            if requirement["maximum"] is not None:
                executed_external_count_bounded_maximum_totals[external] = (
                    executed_external_count_bounded_maximum_totals.get(external, 0)
                    + requirement["maximum"]
                )
        if observed_executed_external_counts is not None:
            for external, count in observed_executed_external_counts.items():
                executed_external_count_observed_totals[external] = (
                    executed_external_count_observed_totals.get(external, 0)
                    + count
                )
        if steps is not None:
            interpreter_steps.append(steps)

        def audit_finding(message: str) -> None:
            findings.append(ValidationFinding("audit", message, "lcnf", case_id))

        if missing_static:
            audit_finding(
                f"missing required static LCNF forms: {','.join(missing_static)}"
            )
        if missing_executed:
            audit_finding(
                "missing required executed LCNF forms: "
                f"{','.join(missing_executed)}"
            )
        if unsatisfied_executed_counts:
            audit_finding(
                "executed LCNF form counts outside required bounds: "
                + render_count_violations(unsatisfied_executed_counts, "form")
            )
        if missing_static_externals:
            audit_finding(
                "missing required static externals: "
                f"{','.join(missing_static_externals)}"
            )
        if missing_executed_externals:
            audit_finding(
                "missing required executed externals: "
                f"{','.join(missing_executed_externals)}"
            )
        if unsatisfied_executed_external_counts:
            audit_finding(
                "executed external counts outside required bounds: "
                + render_count_violations(
                    unsatisfied_executed_external_counts, "external"
                )
            )
        if record is not None and not executed_present:
            audit_finding("missing executed-lcnf-forms diagnostic")
        if record is not None and not executed_counts_present:
            audit_finding("missing executed-lcnf-form-counts diagnostic")
        elif record is not None and observed_executed_counts is None:
            audit_finding(
                "executed-lcnf-form-counts must be a unique JSON array of "
                "positive form counts"
            )
        elif (
            record is not None
            and executed_present
            and sorted(observed_executed_counts) != observed_executed
        ):
            audit_finding(
                "executed-lcnf-form-counts diagnostic disagrees with "
                "executed-lcnf-forms"
            )
        if record is not None and not steps_present:
            audit_finding("missing interpreter-steps diagnostic")
        elif record is not None and steps is None:
            audit_finding("interpreter-steps must be a positive integer")
        if record is not None and not static_external_present:
            audit_finding("missing externals diagnostic")
        if record is not None and not static_external_missing_present:
            audit_finding("missing missing-externals diagnostic")
        elif reported_missing_static_externals != missing_static_externals:
            audit_finding(
                "missing-externals diagnostic disagrees with obligations "
                f"(reported={','.join(reported_missing_static_externals)}; "
                f"computed={','.join(missing_static_externals)})"
            )
        if record is not None and not executed_external_present:
            audit_finding("missing executed-externals diagnostic")
        if record is not None and not executed_external_counts_present:
            audit_finding("missing executed-external-counts diagnostic")
        elif record is not None and observed_executed_external_counts is None:
            audit_finding(
                "executed-external-counts must be a unique JSON array of "
                "positive external counts"
            )
        elif (
            record is not None
            and executed_external_present
            and sorted(observed_executed_external_counts)
            != observed_executed_externals
        ):
            audit_finding(
                "executed-external-counts diagnostic disagrees with "
                "executed-externals"
            )
        if record is not None and not executed_external_missing_present:
            audit_finding("missing missing-executed-externals diagnostic")
        elif reported_missing_executed_externals != missing_executed_externals:
            audit_finding(
                "missing-executed-externals diagnostic disagrees with "
                "obligations "
                f"(reported={','.join(reported_missing_executed_externals)}; "
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
                    "formCounts": {
                        "diagnosticPresent": executed_counts_present,
                        "diagnosticValid": (
                            executed_counts_present
                            and observed_executed_counts is not None
                        ),
                        "obligationsActive": executed_count_obligations_active,
                        "upperBoundsActive": executed_count_upper_bounds_active,
                        "zeroCountsActive": executed_count_zero_counts_active,
                        "required": required_executed_counts,
                        "requiredObservations": required_count_observations(
                            required_executed_counts, observed_count_map, "form"
                        ),
                        "observed": named_count_items(
                            observed_count_map, "form", "count"
                        ),
                        "unsatisfied": unsatisfied_executed_counts,
                    },
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
                        "counts": {
                            "diagnosticPresent": executed_external_counts_present,
                            "diagnosticValid": (
                                executed_external_counts_present
                                and observed_executed_external_counts is not None
                            ),
                            "obligationsActive": (
                                executed_external_count_obligations_active
                            ),
                            "upperBoundsActive": (
                                executed_external_count_upper_bounds_active
                            ),
                            "zeroCountsActive": (
                                executed_external_count_zero_counts_active
                            ),
                            "required": required_executed_external_counts,
                            "requiredObservations": required_count_observations(
                                required_executed_external_counts,
                                observed_external_count_map,
                                "external",
                            ),
                            "observed": named_count_items(
                                observed_external_count_map, "external", "count"
                            ),
                            "unsatisfied": unsatisfied_executed_external_counts,
                        },
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
                "formCounts": {
                    "casesWithRequirements": executed_count_requirement_count,
                    "casesWithUpperBounds": executed_count_upper_bound_case_count,
                    "casesWithZeroRequirements": executed_count_zero_case_count,
                    "zeroRequirementCount": executed_count_zero_requirement_count,
                    "casesWithDiagnostics": executed_count_diagnostic_count,
                    "casesWithValidDiagnostics": (
                        executed_count_valid_diagnostic_count
                    ),
                    "requiredMinimums": named_count_items(
                        executed_count_required_totals, "form", "minimum"
                    ),
                    "boundedMaximums": named_count_items(
                        executed_count_bounded_maximum_totals,
                        "form",
                        "maximum",
                    ),
                    "observed": named_count_items(
                        executed_count_observed_totals, "form", "count"
                    ),
                    "unsatisfiedObligationCount": executed_count_missing_count,
                },
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
                    "counts": {
                        "casesWithRequirements": (
                            executed_external_count_requirement_count
                        ),
                        "casesWithUpperBounds": (
                            executed_external_count_upper_bound_case_count
                        ),
                        "casesWithZeroRequirements": (
                            executed_external_count_zero_case_count
                        ),
                        "zeroRequirementCount": (
                            executed_external_count_zero_requirement_count
                        ),
                        "casesWithDiagnostics": (
                            executed_external_count_diagnostic_count
                        ),
                        "casesWithValidDiagnostics": (
                            executed_external_count_valid_diagnostic_count
                        ),
                        "requiredMinimums": named_count_items(
                            executed_external_count_required_totals,
                            "external",
                            "minimum",
                        ),
                        "boundedMaximums": named_count_items(
                            executed_external_count_bounded_maximum_totals,
                            "external",
                            "maximum",
                        ),
                        "observed": named_count_items(
                            executed_external_count_observed_totals,
                            "external",
                            "count",
                        ),
                        "unsatisfiedObligationCount": (
                            executed_external_count_missing_count
                        ),
                    },
                },
            },
        },
        "cases": cases,
    }
    return report, findings


def write_coverage_artifact(out_dir: Path, report: dict) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "coverage.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


class LcnfAdapter:
    name = "lcnf"

    def __init__(self) -> None:
        self.engine: Path | None = None
        self.lean_path: str | None = None
        self.tools: tuple[ValidationTool, ...] | None = None

    def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
        return prepare_manifest(descriptors)

    def build(self, context: BuildContext) -> None:
        self.engine = None
        self.lean_path = None
        self.tools = None
        if not context.no_build:
            built = run(["lake", "build", "Fir.Validation"], context.root)
            if built.returncode != 0:
                sys.stderr.write(built.stdout + built.stderr)
                raise ValidationError("failed to build LCNF validation backend")
        self.engine = resolve_lake_command(context.root, "lean")
        runner = context.root / "FirValidationLCNF.lean"
        module = (
            context.root
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Fir"
            / "Validation"
            / "LCNF.olean"
        )
        self.tools = (
            validation_tool_from_file(
                self.name, "engine", "lean-toolchain/bin/lean", self.engine
            ),
            validation_tool_from_file(
                self.name, "runner-source", "FirValidationLCNF.lean", runner
            ),
            validation_tool_from_file(
                self.name,
                "module",
                ".lake/build/lib/lean/Fir/Validation/LCNF.olean",
                module,
            ),
        )
        environment = run(
            ["lake", "env", "printenv", "LEAN_PATH"], context.root
        )
        if environment.returncode != 0 or not environment.stdout.strip():
            raise ValidationError("failed to resolve LCNF validation LEAN_PATH")
        self.lean_path = environment.stdout.strip()

    def verify_tools(self) -> None:
        if self.engine is None or self.tools is None:
            raise ValidationError("LCNF adapter must be built before execution")
        current: list[ValidationTool] = []
        for tool in self.tools:
            if tool.source_path is None:
                raise ValidationError("LCNF tool has no source path")
            current.append(
                validation_tool_from_file(
                    tool.backend,
                    tool.kind,
                    tool.name,
                    tool.source_path,
                )
            )
        if tuple(current) != self.tools:
            raise ValidationError("LCNF validation tools changed during run")

    def execute(self, context: RunContext) -> BackendRun:
        self.verify_tools()
        if self.engine is None or self.lean_path is None or self.tools is None:
            raise ValidationError("LCNF adapter must be built before execution")
        command = [str(self.engine), "FirValidationLCNF.lean"]
        completed = run(
            command,
            context.root,
            extra_env={"LEAN_PATH": self.lean_path},
        )
        execution_artifacts = write_process_artifacts(
            context.out_dir / self.name, completed, self.name
        )
        self.verify_tools()
        backend_run = BackendRun(
            self.name,
            context.all_cases,
            tools=list(self.tools),
            artifacts=list(execution_artifacts),
        )
        if completed.returncode != 0:
            backend_run.findings.append(
                ValidationFinding(
                    "execution",
                    f"process exited {completed.returncode}",
                    self.name,
                )
            )
            backend_run.blocked_cases.update(context.selected)
            return backend_run
        backend_run.results = result_map(
            records_from_output(completed.stdout, command), self.name
        )
        return backend_run

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        report, findings = coverage_report(
            context.descriptors, backend_run.results, context.selected
        )
        write_coverage_artifact(context.out_dir / self.name, report)
        return BackendAudit(report, findings)
