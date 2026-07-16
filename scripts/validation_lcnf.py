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
    "requiredExternals",
    "requiredExecutedExternals",
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

        required_forms = checked_names("requiredLcnfForms")
        required_executed_forms = checked_names("requiredExecutedLcnfForms")
        required_externals = checked_names("requiredExternals")
        required_executed_externals = checked_names("requiredExecutedExternals")
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
        item["requiredExternals"] = required_externals
        item["requiredExecutedExternals"] = required_executed_externals
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
        if record is not None and not executed_present:
            audit_finding("missing executed-lcnf-forms diagnostic")
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
        write_process_artifacts(context.out_dir / self.name, completed)
        self.verify_tools()
        backend_run = BackendRun(
            self.name,
            context.all_cases,
            tools=list(self.tools),
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
