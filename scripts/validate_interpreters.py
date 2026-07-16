#!/usr/bin/env python3
"""Run FIR's native oracle and final-impure LCNF candidate on one corpus."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


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
}


class ValidationError(RuntimeError):
    pass


def run(command: list[str], timeout: int = 120) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            cwd=ROOT,
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

        descriptor = dict(value)
        descriptor["tags"] = sorted(tags)
        descriptor["requiredLcnfForms"] = sorted(required_forms)
        descriptor["requiredExecutedLcnfForms"] = sorted(required_executed_forms)
        descriptor["requiredExternals"] = sorted(required_externals)
        descriptor["requiredExecutedExternals"] = sorted(required_executed_externals)
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


def compare_success(native: dict, candidate: dict) -> tuple[bool, dict, dict]:
    native_observation = success_observation(native)
    candidate_observation = success_observation(candidate)
    return native_observation == candidate_observation, native_observation, candidate_observation


def write_artifact(out_dir: Path, case_id: str, backend: str, record: dict) -> None:
    destination = out_dir / case_id / backend
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "result.json").write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="compare Lean native execution with FIR's final-impure interpreter"
    )
    parser.add_argument("--case", action="append", dest="cases", help="run only this case ID")
    parser.add_argument("--tag", help="run cases carrying this corpus tag")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--no-build", action="store_true", help="reuse the existing native executable")
    args = parser.parse_args()

    if not args.no_build:
        built = run(["lake", "build", "fir-native-oracle", "Fir.Validation"])
        if built.returncode != 0:
            sys.stderr.write(built.stdout + built.stderr)
            raise ValidationError("failed to build validation backends")

    manifest_command = ["lake", "exe", "fir-native-oracle", "--manifest"]
    manifested = run(manifest_command)
    if manifested.returncode != 0:
        raise ValidationError(f"failed to read corpus manifest:\n{manifested.stderr}")
    descriptors = manifest_from_output(manifested.stdout, manifest_command)
    descriptor_by_id = {descriptor["id"]: descriptor for descriptor in descriptors}
    all_cases = [descriptor["id"] for descriptor in descriptors]
    selected = select_cases(descriptors, args.cases, args.tag)
    write_corpus_manifest(args.out_dir, descriptors)

    lcnf_command = ["lake", "env", "lean", "FirValidationLCNF.lean"]
    lcnf_run = run(lcnf_command)
    (args.out_dir / "lcnf").mkdir(parents=True, exist_ok=True)
    (args.out_dir / "lcnf" / "stdout.jsonl").write_text(lcnf_run.stdout, encoding="utf-8")
    (args.out_dir / "lcnf" / "stderr.log").write_text(lcnf_run.stderr, encoding="utf-8")
    if lcnf_run.returncode != 0:
        raise ValidationError(f"LCNF backend failed:\n{lcnf_run.stdout}{lcnf_run.stderr}")
    lcnf_results = result_map(records_from_output(lcnf_run.stdout, lcnf_command), "lcnf")

    coverage, coverage_failures = coverage_report(descriptors, lcnf_results, selected)
    write_coverage_artifact(args.out_dir, coverage)
    failures: list[str] = list(coverage_failures)
    coverage_failed_cases = {
        failure.split(":", maxsplit=1)[0] for failure in coverage_failures
    }
    comparisons: list[dict] = []
    for case_id in selected:
        native_command = ["lake", "exe", "fir-native-oracle", "--case", case_id]
        native_run = run(native_command)
        if native_run.returncode != 0:
            failures.append(f"{case_id}: native process exited {native_run.returncode}")
            continue
        native_records = records_from_output(native_run.stdout, native_command)
        native_results = result_map(native_records, "native")
        if set(native_results) != {case_id}:
            failures.append(f"{case_id}: native backend returned {sorted(native_results)}")
            continue
        native = native_results[case_id]
        candidate = lcnf_results.get(case_id)
        if candidate is None:
            failures.append(f"{case_id}: LCNF backend returned no result")
            continue
        write_artifact(args.out_dir, case_id, "native", native)
        write_artifact(args.out_dir, case_id, "lcnf", candidate)
        native_dir = args.out_dir / case_id / "native"
        (native_dir / "stdout.jsonl").write_text(native_run.stdout, encoding="utf-8")
        (native_dir / "stderr.log").write_text(native_run.stderr, encoding="utf-8")
        if case_id in coverage_failed_cases:
            continue
        try:
            equal, native_observation, lcnf_observation = compare_success(native, candidate)
        except ValidationError as error:
            failures.append(str(error))
            continue
        if not equal:
            failures.append(
                f"{case_id}: semantic mismatch\n"
                f"  native={json.dumps(native_observation, sort_keys=True)}\n"
                f"  lcnf={json.dumps(lcnf_observation, sort_keys=True)}"
            )
            continue
        comparisons.append(
            {
                "caseId": case_id,
                "oracle": "native",
                "candidate": "lcnf",
                "equal": True,
                "case": descriptor_by_id[case_id],
            }
        )
        forms = diagnostics(candidate).get("lcnf-forms", "-")
        print(f"PASS {case_id:<22} lcnf=[{forms}]")

    extra_lcnf = sorted(set(lcnf_results) - set(all_cases))
    missing_lcnf = sorted(set(all_cases) - set(lcnf_results))
    if extra_lcnf:
        failures.append(f"LCNF backend returned unknown cases: {', '.join(extra_lcnf)}")
    if missing_lcnf:
        failures.append(f"LCNF backend omitted cases: {', '.join(missing_lcnf)}")

    if failures:
        for failure in failures:
            print(f"FAIL {failure}", file=sys.stderr)
        return 1
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "comparison.json").write_text(
        json.dumps({"version": PROTOCOL_VERSION, "comparisons": comparisons}, indent=2)
        + "\n",
        encoding="utf-8",
    )
    print(f"validated {len(selected)} case(s): native == final-impure LCNF")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validation harness error: {error}", file=sys.stderr)
        raise SystemExit(2)
