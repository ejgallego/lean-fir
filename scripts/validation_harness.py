#!/usr/bin/env python3
"""Compare Lean's native oracle with protocol-compatible candidate backends."""

from __future__ import annotations

import json
import os
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Protocol


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
    "effectProjections",
}
EFFECT_PROJECTION_FIELDS = {"external", "operation", "argSchemas", "resultSchema"}


class ValidationError(RuntimeError):
    pass


@dataclass(frozen=True)
class ValidationFinding:
    phase: str
    message: str
    backend: str | None = None
    case_id: str | None = None

    def render(self) -> str:
        scope = [value for value in (self.case_id, self.backend) if value is not None]
        prefix = f"{': '.join(scope)}: " if scope else ""
        return prefix + self.message

    def to_json(self) -> dict:
        result = {"phase": self.phase, "message": self.message}
        if self.backend is not None:
            result["backend"] = self.backend
        if self.case_id is not None:
            result["caseId"] = self.case_id
        return result


def run(
    command: list[str],
    cwd: Path,
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
            cwd=cwd,
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
    """Parse neutral descriptors while preserving backend extension fields."""
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
            missing = (
                sorted(MANIFEST_FIELDS - value.keys())
                if isinstance(value, dict)
                else []
            )
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
        descriptor = dict(value)
        descriptor["tags"] = sorted(tags)
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


def result_domain_findings(
    results: dict[str, dict], backend: str, expected_cases: list[str]
) -> list[ValidationFinding]:
    """Check which case IDs a backend returned, independently of how it ran."""
    expected = set(expected_cases)
    actual = set(results)
    findings: list[ValidationFinding] = []
    unknown = sorted(actual - expected)
    missing = sorted(expected - actual)
    for case_id in unknown:
        findings.append(
            ValidationFinding(
                "result-domain",
                "backend returned an unknown case",
                backend,
                case_id,
            )
        )
    for case_id in missing:
        findings.append(
            ValidationFinding(
                "result-domain",
                "backend omitted the expected case",
                backend,
                case_id,
            )
        )
    return findings


def compare_backend_results(
    descriptor_by_id: dict[str, dict],
    selected: list[str],
    reference_backend: str,
    reference_results: dict[str, dict],
    candidate_backend: str,
    candidate_results: dict[str, dict],
    blocked_cases: set[str] | None = None,
) -> tuple[list[dict], list[ValidationFinding]]:
    """Compare semantic observations without imposing candidate-specific policy."""
    blocked = blocked_cases or set()
    comparisons: list[dict] = []
    findings: list[ValidationFinding] = []
    for case_id in selected:
        if case_id in blocked:
            continue
        reference = reference_results.get(case_id)
        if reference is None:
            findings.append(
                ValidationFinding(
                    "comparison",
                    "backend returned no result to compare",
                    reference_backend,
                    case_id,
                )
            )
            continue
        candidate = candidate_results.get(case_id)
        if candidate is None:
            findings.append(
                ValidationFinding(
                    "comparison",
                    "backend returned no result to compare",
                    candidate_backend,
                    case_id,
                )
            )
            continue
        try:
            reference_observation = success_observation(reference)
        except ValidationError as error:
            findings.append(
                ValidationFinding(
                    "comparison", str(error), reference_backend, case_id
                )
            )
            continue
        try:
            candidate_observation = success_observation(candidate)
        except ValidationError as error:
            findings.append(
                ValidationFinding(
                    "comparison", str(error), candidate_backend, case_id
                )
            )
            continue
        equal = reference_observation == candidate_observation
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
            findings.append(
                ValidationFinding(
                    "comparison",
                    "semantic mismatch\n"
                    f"  {reference_backend}="
                    f"{json.dumps(reference_observation, sort_keys=True)}\n"
                    f"  {candidate_backend}="
                    f"{json.dumps(candidate_observation, sort_keys=True)}",
                    case_id=case_id,
                )
            )
    return comparisons, findings

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
    findings: list[ValidationFinding] | None = None,
    selected_count: int | None = None,
) -> None:
    recorded_findings = findings or []
    selected = len(comparisons) if selected_count is None else selected_count
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "comparison.json").write_text(
        json.dumps(
            {
                "version": PROTOCOL_VERSION,
                "reference": reference_backend,
                "candidate": candidate_backend,
                "comparisons": comparisons,
                "findings": [finding.to_json() for finding in recorded_findings],
                "summary": {
                    "selectedCases": selected,
                    "comparedCases": len(comparisons),
                    "equalCases": sum(
                        int(comparison["equal"]) for comparison in comparisons
                    ),
                    "findingCount": len(recorded_findings),
                },
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
    findings: list[ValidationFinding] = field(default_factory=list)
    blocked_cases: set[str] = field(default_factory=set)


@dataclass
class BackendAudit:
    report: dict | None = None
    findings: list[ValidationFinding] = field(default_factory=list)


class BackendAdapter(Protocol):
    name: str

    def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
        ...

    def build(self, context: BuildContext) -> None:
        ...

    def execute(self, context: RunContext) -> BackendRun:
        ...

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        ...


@dataclass(frozen=True)
class ExternalCommandAdapter:
    """Protocol adapter driven by shell-free commands from a JSON config."""

    name: str
    run_command: list[str]
    result_domain: str
    build_command: list[str] = field(default_factory=list)
    timeout_seconds: int = 120

    def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
        return descriptors

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
            context.root,
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
        completed = run(
            self.run_command,
            context.root,
            self.timeout_seconds,
            environment,
        )
        write_process_artifacts(destination, completed)
        expected_cases = (
            context.selected
            if self.result_domain == "selected"
            else context.all_cases
        )
        backend_run = BackendRun(self.name, list(expected_cases))
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
def validate_pair(
    context: RunContext,
    reference: BackendAdapter,
    candidate: BackendAdapter,
) -> tuple[list[dict], list[ValidationFinding]]:
    """Execute, audit, persist, and compare one reference/candidate pair."""
    reference_run = reference.execute(context)
    candidate_run = candidate.execute(context)
    findings = list(reference_run.findings) + list(candidate_run.findings)
    findings.extend(
        result_domain_findings(
            reference_run.results, reference.name, reference_run.expected_cases
        )
    )
    findings.extend(
        result_domain_findings(
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
    findings.extend(reference_audit.findings)
    findings.extend(candidate_audit.findings)

    comparisons, comparison_findings = compare_backend_results(
        context.descriptor_by_id,
        context.selected,
        reference.name,
        reference_run.results,
        candidate.name,
        candidate_run.results,
        reference_run.blocked_cases | candidate_run.blocked_cases,
    )
    findings.extend(comparison_findings)
    write_comparison_artifact(
        context.out_dir,
        reference.name,
        candidate.name,
        comparisons,
        findings,
        len(context.selected),
    )
    return comparisons, findings
