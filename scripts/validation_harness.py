#!/usr/bin/env python3
"""Compare Lean's native oracle with protocol-compatible candidate backends."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
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
BACKEND_NAME_CHARACTERS = "abcdefghijklmnopqrstuvwxyz0123456789-_"


class ValidationError(RuntimeError):
    pass


def validate_backend_name(name: object, context: str = "backend") -> str:
    if (
        not isinstance(name, str)
        or not name
        or not name[0].isalpha()
        or any(character not in BACKEND_NAME_CHARACTERS for character in name)
    ):
        raise ValidationError(
            f"{context}: name must use lowercase letters, digits, '-' or '_'"
        )
    return name


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


@dataclass(frozen=True)
class ValidationInput:
    kind: str
    name: str
    sha256: str
    content: bytes | None = field(default=None, compare=False, repr=False)

    def to_json(self) -> dict[str, str]:
        return {"kind": self.kind, "name": self.name, "sha256": self.sha256}


@dataclass(frozen=True)
class ProductDeclaration:
    kind: str
    path: str


@dataclass(frozen=True)
class ValidationProduct:
    backend: str
    kind: str
    name: str
    sha256: str

    def to_json(self) -> dict[str, str]:
        return {
            "backend": self.backend,
            "kind": self.kind,
            "name": self.name,
            "sha256": self.sha256,
        }


def sha256_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def canonical_json_sha256(value: object) -> str:
    content = json.dumps(
        value,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")
    return sha256_bytes(content)


def validation_selection_sha256(
    corpus_sha256: str, selected_cases: list[str]
) -> str:
    return canonical_json_sha256(
        {
            "version": PROTOCOL_VERSION,
            "corpusSha256": corpus_sha256,
            "selectedCases": selected_cases,
        }
    )


def validation_run_sha256(
    selection_sha256: str,
    backend_names: list[str],
    pair_names: list[tuple[str, str]],
    inputs: tuple[ValidationInput, ...],
    products: list[ValidationProduct],
) -> str:
    return canonical_json_sha256(
        {
            "version": PROTOCOL_VERSION,
            "selectionSha256": selection_sha256,
            "backends": backend_names,
            "pairs": [
                {"reference": reference, "candidate": candidate}
                for reference, candidate in pair_names
            ],
            "inputs": [item.to_json() for item in inputs],
            "products": [product.to_json() for product in products],
        }
    )


def validation_input_from_file(
    kind: str, path: Path, root: Path
) -> ValidationInput:
    try:
        content = path.read_bytes()
    except OSError as error:
        raise ValidationError(f"cannot hash validation input {path}: {error}") from error
    resolved = path.resolve()
    digest = sha256_bytes(content)
    try:
        name = resolved.relative_to(root.resolve()).as_posix()
    except ValueError:
        name = f"external/{digest}/{resolved.name}"
    return ValidationInput(kind, name, digest, content)


def checked_relative_posix_path(value: object, context: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValidationError(
            f"{context}: path must be a nonempty relative POSIX path"
        )
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or not path.parts
        or "\\" in value
        or value != path.as_posix()
        or any(part in ("", ".", "..") for part in path.parts)
    ):
        raise ValidationError(
            f"{context}: path must be a normalized relative POSIX path"
        )
    return value


def checked_sha256(value: object, context: str) -> str:
    if (
        not isinstance(value, str)
        or len(value) != 64
        or any(character not in "0123456789abcdef" for character in value)
    ):
        raise ValidationError(f"{context}: malformed SHA-256")
    return value


def validation_product_from_file(
    backend: str,
    declaration: ProductDeclaration,
    out_dir: Path,
) -> ValidationProduct:
    backend_name = validate_backend_name(backend)
    kind = validate_backend_name(declaration.kind, f"{backend_name} product kind")
    product_path = checked_relative_posix_path(
        declaration.path, f"{backend_name} product"
    )
    backend_root = (out_dir / backend_name).resolve()
    path = backend_root.joinpath(*PurePosixPath(product_path).parts)
    resolved = path.resolve()
    try:
        resolved.relative_to(backend_root)
    except ValueError as error:
        raise ValidationError(
            f"{backend_name} product escapes its output directory: "
            f"{product_path}"
        ) from error
    if path.is_symlink() or not path.is_file():
        raise ValidationError(
            f"{backend_name} product is not a regular file: {product_path}"
        )
    try:
        content = path.read_bytes()
    except OSError as error:
        raise ValidationError(
            f"cannot hash {backend_name} product {product_path}: {error}"
        ) from error
    return ValidationProduct(
        backend_name,
        kind,
        product_path,
        sha256_bytes(content),
    )


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


def corpus_artifact_bytes(descriptors: list[dict]) -> bytes:
    return (
        json.dumps(
            {"version": PROTOCOL_VERSION, "cases": descriptors},
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def write_corpus_manifest(out_dir: Path, descriptors: list[dict]) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "corpus.json").write_bytes(corpus_artifact_bytes(descriptors))


def retain_evidence_blob(
    out_dir: Path, category: str, digest: str, content: bytes
) -> str:
    checked_relative_posix_path(category, "evidence category")
    checked_sha256(digest, "evidence blob")
    if sha256_bytes(content) != digest:
        raise ValidationError(f"evidence content disagrees with SHA-256: {digest}")
    root = out_dir.resolve()
    directory = root
    for part in ("evidence", *PurePosixPath(category).parts):
        directory = directory / part
        if directory.is_symlink():
            raise ValidationError(
                f"evidence directory contains a symlink: {directory}"
            )
        try:
            directory.mkdir(exist_ok=True)
        except OSError as error:
            raise ValidationError(
                f"cannot create evidence directory {directory}: {error}"
            ) from error
        if not directory.is_dir():
            raise ValidationError(f"evidence path is not a directory: {directory}")
    artifact = directory / digest
    if artifact.is_symlink() or (artifact.exists() and not artifact.is_file()):
        raise ValidationError(f"evidence blob is not a regular file: {artifact}")
    if artifact.exists():
        try:
            existing = artifact.read_bytes()
        except OSError as error:
            raise ValidationError(
                f"cannot read retained evidence blob {artifact}: {error}"
            ) from error
        if existing != content:
            raise ValidationError(
                f"retained evidence blob disagrees with SHA-256: {digest}"
            )
    else:
        temporary_path: Path | None = None
        try:
            with tempfile.NamedTemporaryFile(
                dir=directory,
                prefix=".validation-evidence-",
                delete=False,
            ) as temporary:
                temporary.write(content)
                temporary.flush()
                os.fsync(temporary.fileno())
                temporary_path = Path(temporary.name)
            os.link(temporary_path, artifact)
        except FileExistsError:
            try:
                existing = artifact.read_bytes()
            except OSError as error:
                raise ValidationError(
                    f"cannot read concurrently retained evidence blob "
                    f"{artifact}: {error}"
                ) from error
            if existing != content:
                raise ValidationError(
                    f"retained evidence blob disagrees with SHA-256: {digest}"
                )
        except OSError as error:
            raise ValidationError(
                f"cannot retain evidence blob {artifact}: {error}"
            ) from error
        finally:
            if temporary_path is not None:
                try:
                    temporary_path.unlink(missing_ok=True)
                except OSError as error:
                    raise ValidationError(
                        f"cannot remove temporary evidence blob "
                        f"{temporary_path}: {error}"
                    ) from error
    return artifact.relative_to(root).as_posix()


def retain_validation_inputs(
    context: RunContext,
    inputs: tuple[ValidationInput, ...],
) -> list[dict[str, str]]:
    retained: list[dict[str, str]] = []
    for index, item in enumerate(inputs):
        validate_backend_name(item.kind, "validation input kind")
        checked_relative_posix_path(item.name, "validation input name")
        digest = checked_sha256(item.sha256, "validation input")
        if index == 0:
            if item.kind != "corpus" or item.name != "corpus.json":
                raise ValidationError("first validation input must be corpus.json")
            content = corpus_artifact_bytes(context.descriptors)
        else:
            if item.content is None:
                raise ValidationError(
                    f"validation input has no retainable source: "
                    f"{item.kind}:{item.name}"
                )
            content = item.content
        retained.append(
            {
                **item.to_json(),
                "artifact": retain_evidence_blob(
                    context.out_dir, "inputs", digest, content
                ),
            }
        )
    return retained


def retain_validation_products(
    context: RunContext,
    products: list[ValidationProduct],
) -> list[dict[str, str]]:
    retained: list[dict[str, str]] = []
    for product in products:
        captured = validation_product_from_file(
            product.backend,
            ProductDeclaration(product.kind, product.name),
            context.out_dir,
        )
        if captured != product:
            raise ValidationError(
                f"validation product changed before evidence retention: "
                f"{product.backend}:{product.kind}:{product.name}"
            )
        source = context.out_dir / product.backend / product.name
        try:
            content = source.read_bytes()
        except OSError as error:
            raise ValidationError(
                f"cannot retain validation product {source}: {error}"
            ) from error
        retained.append(
            {
                **product.to_json(),
                "artifact": retain_evidence_blob(
                    context.out_dir, "products", product.sha256, content
                ),
            }
        )
    return retained


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
    destination = comparison_artifact_path(
        out_dir, reference_backend, candidate_backend
    )
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(
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


def comparison_artifact_path(
    out_dir: Path, reference_backend: str, candidate_backend: str
) -> Path:
    reference = validate_backend_name(reference_backend, "reference backend")
    candidate = validate_backend_name(candidate_backend, "candidate backend")
    return out_dir / "comparisons" / f"{reference}--{candidate}.json"


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
    inputs: tuple[ValidationInput, ...] = ()

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
    products: list[ValidationProduct] = field(default_factory=list)


@dataclass
class BackendAudit:
    report: dict | None = None
    findings: list[ValidationFinding] = field(default_factory=list)


PRODUCT_RECEIPT_DIAGNOSTIC = "validation-products"


def product_receipt_value(products: list[ValidationProduct]) -> str:
    entries = sorted(
        (
            {
                "kind": product.kind,
                "name": product.name,
                "sha256": product.sha256,
            }
            for product in products
        ),
        key=lambda entry: (entry["kind"], entry["name"], entry["sha256"]),
    )
    return json.dumps(entries, separators=(",", ":"), sort_keys=True)


def product_receipt_findings(backend_run: BackendRun) -> list[ValidationFinding]:
    if not backend_run.products:
        return []
    declared = {
        (product.kind, product.name, product.sha256)
        for product in backend_run.products
    }
    findings: list[ValidationFinding] = []

    def finding(message: str, case_id: str | None = None) -> None:
        findings.append(
            ValidationFinding("audit", message, backend_run.backend, case_id)
        )

    for case_id, record in sorted(backend_run.results.items()):
        diagnostics = record.get("diagnostics", [])
        if not isinstance(diagnostics, list) or not all(
            isinstance(item, dict) for item in diagnostics
        ):
            finding("malformed diagnostics while reading product receipt", case_id)
            continue
        receipts = [
            item for item in diagnostics
            if item.get("key") == PRODUCT_RECEIPT_DIAGNOSTIC
        ]
        if not receipts:
            finding("missing validation-products diagnostic", case_id)
            continue
        if len(receipts) != 1 or set(receipts[0]) != {"key", "value"}:
            finding("malformed validation-products diagnostic", case_id)
            continue
        try:
            value = json.loads(receipts[0]["value"])
        except (TypeError, json.JSONDecodeError):
            finding("malformed validation-products diagnostic", case_id)
            continue
        if not isinstance(value, list):
            finding("malformed validation-products diagnostic", case_id)
            continue
        reported: list[tuple[str, str, str]] = []
        malformed = False
        for entry in value:
            if not isinstance(entry, dict) or set(entry) != {
                "kind", "name", "sha256"
            }:
                malformed = True
                break
            kind = entry["kind"]
            name = entry["name"]
            sha256 = entry["sha256"]
            if not all(isinstance(item, str) for item in (kind, name, sha256)):
                malformed = True
                break
            reported.append((kind, name, sha256))
        if malformed or len(set(reported)) != len(reported):
            finding("malformed validation-products diagnostic", case_id)
            continue
        if not reported:
            finding(
                "validation-products diagnostic reports no consumed products",
                case_id,
            )
            continue
        unknown = sorted(set(reported) - declared)
        if unknown:
            finding(
                "product receipt contains undeclared products: "
                + ", ".join(
                    f"{kind}:{name}@{sha256}" for kind, name, sha256 in unknown
                ),
                case_id,
            )
    return findings


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


@dataclass
class ExternalCommandAdapter:
    """Protocol adapter driven by shell-free commands from a JSON config."""

    name: str
    run_command: list[str]
    result_domain: str
    build_command: list[str] = field(default_factory=list)
    timeout_seconds: int = 120
    product_declarations: tuple[ProductDeclaration, ...] = ()
    _built_products: tuple[ValidationProduct, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )

    def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
        return descriptors

    def environment(self, out_dir: Path) -> dict[str, str]:
        return {
            "FIR_VALIDATION_BACKEND": self.name,
            "FIR_VALIDATION_OUT_DIR": str((out_dir / self.name).resolve()),
            "FIR_VALIDATION_PROTOCOL_VERSION": str(PROTOCOL_VERSION),
        }

    def collect_products(self, out_dir: Path) -> tuple[ValidationProduct, ...]:
        return tuple(
            validation_product_from_file(self.name, declaration, out_dir)
            for declaration in sorted(
                self.product_declarations,
                key=lambda item: (item.kind, item.path),
            )
        )

    def remove_stale_products(self, out_dir: Path) -> None:
        backend_root = (out_dir / self.name).resolve()
        for declaration in self.product_declarations:
            path = backend_root.joinpath(*PurePosixPath(declaration.path).parts)
            if path.is_symlink() or path.is_file():
                try:
                    path.unlink()
                except OSError as error:
                    raise ValidationError(
                        f"cannot remove stale {self.name} product "
                        f"{declaration.path}: {error}"
                    ) from error
            elif path.exists():
                raise ValidationError(
                    f"{self.name} product path is not a regular file: "
                    f"{declaration.path}"
                )

    def build(self, context: BuildContext) -> None:
        self._built_products = None
        if not context.no_build and self.build_command:
            destination = context.out_dir / self.name / "build"
            destination.mkdir(parents=True, exist_ok=True)
            self.remove_stale_products(context.out_dir)
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
        self._built_products = self.collect_products(context.out_dir)

    def execute(self, context: RunContext) -> BackendRun:
        destination = context.out_dir / self.name
        destination.mkdir(parents=True, exist_ok=True)
        if self._built_products is None:
            raise ValidationError(
                f"{self.name} adapter must be built before execution"
            )
        if self.collect_products(context.out_dir) != self._built_products:
            raise ValidationError(
                f"{self.name} products changed between build and execution"
            )
        environment = self.environment(context.out_dir)
        environment.update(
            {
                "FIR_VALIDATION_CASES": json.dumps(
                    context.selected, separators=(",", ":")
                ),
                "FIR_VALIDATION_CORPUS": str(
                    (context.out_dir / "corpus.json").resolve()
                ),
                "FIR_VALIDATION_PRODUCTS": json.dumps(
                    [
                        {
                            **product.to_json(),
                            "path": str(
                                (
                                    context.out_dir
                                    / product.backend
                                    / product.name
                                ).resolve()
                            ),
                        }
                        for product in self._built_products
                    ],
                    separators=(",", ":"),
                    sort_keys=True,
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
        if self.collect_products(context.out_dir) != self._built_products:
            raise ValidationError(
                f"{self.name} products changed during execution"
            )
        expected_cases = (
            context.selected
            if self.result_domain == "selected"
            else context.all_cases
        )
        backend_run = BackendRun(
            self.name,
            list(expected_cases),
            products=list(self._built_products),
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
            records_from_output(completed.stdout, self.run_command), self.name
        )
        return backend_run

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        return BackendAudit(findings=product_receipt_findings(backend_run))


def external_adapter_from_config(
    path: Path, content: bytes | None = None
) -> ExternalCommandAdapter:
    """Load a declarative external adapter while rejecting shell commands."""
    try:
        source = path.read_bytes() if content is None else content
        value = json.loads(source.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot read adapter config {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValidationError(f"adapter config {path}: expected a JSON object")
    required = {"name", "runCommand", "resultDomain"}
    optional = {"buildCommand", "timeoutSeconds", "products"}
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

    name = validate_backend_name(value["name"], f"adapter config {path}")

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
    raw_products = value.get("products", [])
    if not isinstance(raw_products, list):
        raise ValidationError(
            f"adapter config {path}: products must be an object array"
        )
    product_declarations: list[ProductDeclaration] = []
    product_paths: set[str] = set()
    for index, product in enumerate(raw_products):
        product_context = f"adapter config {path}/products/{index}"
        if not isinstance(product, dict) or set(product) != {"kind", "path"}:
            raise ValidationError(
                f"{product_context}: expected kind and path fields"
            )
        kind = validate_backend_name(product["kind"], product_context)
        product_path = checked_relative_posix_path(
            product["path"], product_context
        )
        if product_path in product_paths:
            raise ValidationError(
                f"adapter config {path}: duplicate product path: {product_path}"
            )
        product_paths.add(product_path)
        product_declarations.append(ProductDeclaration(kind, product_path))
    if product_declarations and not build_command:
        raise ValidationError(
            f"adapter config {path}: products require buildCommand"
        )
    return ExternalCommandAdapter(
        name=name,
        run_command=run_command,
        result_domain=result_domain,
        build_command=build_command,
        timeout_seconds=timeout_seconds,
        product_declarations=tuple(
            sorted(
                product_declarations,
                key=lambda declaration: (declaration.kind, declaration.path),
            )
        ),
    )


@dataclass(frozen=True)
class ValidationPlan:
    adapter_configs: tuple[Path, ...]
    pairs: tuple[tuple[str, str], ...]


def validation_plan_from_config(
    path: Path, content: bytes | None = None
) -> ValidationPlan:
    """Load a strict matrix plan, resolving adapter paths beside the plan."""
    try:
        source = path.read_bytes() if content is None else content
        value = json.loads(source.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot read validation plan {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValidationError(f"validation plan {path}: expected a JSON object")
    required = {"version", "adapterConfigs", "pairs"}
    missing = sorted(required - value.keys())
    unknown = sorted(value.keys() - required)
    if missing:
        raise ValidationError(
            f"validation plan {path}: missing fields: {', '.join(missing)}"
        )
    if unknown:
        raise ValidationError(
            f"validation plan {path}: unknown fields: {', '.join(unknown)}"
        )
    version = value["version"]
    if (
        not isinstance(version, int)
        or isinstance(version, bool)
        or version != PROTOCOL_VERSION
    ):
        raise ValidationError(
            f"validation plan {path}: version {version} "
            f"is not {PROTOCOL_VERSION}"
        )

    raw_configs = value["adapterConfigs"]
    if not isinstance(raw_configs, list) or not all(
        isinstance(config, str) and config for config in raw_configs
    ):
        raise ValidationError(
            f"validation plan {path}: adapterConfigs must be a path array"
        )
    adapter_configs = tuple(
        (
            Path(config)
            if Path(config).is_absolute()
            else path.parent / config
        ).resolve()
        for config in raw_configs
    )
    if len(set(adapter_configs)) != len(adapter_configs):
        raise ValidationError(
            f"validation plan {path}: duplicate adapterConfigs"
        )

    raw_pairs = value["pairs"]
    if not isinstance(raw_pairs, list) or not raw_pairs:
        raise ValidationError(
            f"validation plan {path}: pairs must be a nonempty object array"
        )
    pairs: list[tuple[str, str]] = []
    for index, pair in enumerate(raw_pairs):
        pair_context = f"validation plan {path}/pairs/{index}"
        if not isinstance(pair, dict) or set(pair) != {"reference", "candidate"}:
            raise ValidationError(
                f"{pair_context}: expected reference and candidate fields"
            )
        reference = validate_backend_name(pair["reference"], pair_context)
        candidate = validate_backend_name(pair["candidate"], pair_context)
        if reference == candidate:
            raise ValidationError(
                f"{pair_context}: comparison backends must be distinct"
            )
        pairs.append((reference, candidate))
    if len(set(pairs)) != len(pairs):
        raise ValidationError(
            f"validation plan {path}: duplicate comparison pairs"
        )
    return ValidationPlan(adapter_configs, tuple(pairs))


@dataclass
class PairValidationResult:
    reference: str
    candidate: str
    comparisons: list[dict]
    findings: list[ValidationFinding]


def write_matrix_artifact(
    context: RunContext,
    backend_names: list[str],
    pair_results: list[PairValidationResult],
    findings: list[ValidationFinding],
    products: tuple[ValidationProduct, ...] = (),
) -> None:
    context.out_dir.mkdir(parents=True, exist_ok=True)
    inputs = (
        ValidationInput(
            "corpus",
            "corpus.json",
            sha256_bytes(corpus_artifact_bytes(context.descriptors)),
        ),
        *context.inputs,
    )
    input_keys = [(item.kind, item.name) for item in inputs]
    if len(set(input_keys)) != len(input_keys):
        raise ValidationError("validation matrix contains duplicate provenance inputs")
    retained_inputs = retain_validation_inputs(context, inputs)
    sorted_products = sorted(
        products,
        key=lambda product: (product.backend, product.kind, product.name),
    )
    for product in sorted_products:
        validate_backend_name(product.backend, "validation product backend")
        validate_backend_name(product.kind, "validation product kind")
        checked_relative_posix_path(product.name, "validation product")
        if product.backend not in backend_names:
            raise ValidationError(
                f"validation product names inactive backend: {product.backend}"
            )
        checked_sha256(product.sha256, "validation product")
    product_keys = [
        (product.backend, product.kind, product.name)
        for product in sorted_products
    ]
    if len(set(product_keys)) != len(product_keys):
        raise ValidationError("validation matrix contains duplicate backend products")
    retained_products = retain_validation_products(context, sorted_products)
    pairs = []
    for result in pair_results:
        artifact = comparison_artifact_path(
            context.out_dir, result.reference, result.candidate
        )
        try:
            comparison_content = artifact.read_bytes()
        except OSError as error:
            raise ValidationError(
                f"cannot retain validation comparison {artifact}: {error}"
            ) from error
        comparison_sha256 = sha256_bytes(comparison_content)
        pairs.append(
            {
                "reference": result.reference,
                "candidate": result.candidate,
                "artifact": retain_evidence_blob(
                    context.out_dir,
                    "comparisons",
                    comparison_sha256,
                    comparison_content,
                ),
                "sha256": comparison_sha256,
                "comparedCases": len(result.comparisons),
                "equalCases": sum(
                    int(comparison["equal"])
                    for comparison in result.comparisons
                ),
                "findingCount": len(result.findings),
            }
        )
    selection_sha256 = validation_selection_sha256(
        inputs[0].sha256, list(context.selected)
    )
    run_sha256 = validation_run_sha256(
        selection_sha256,
        backend_names,
        [
            (result.reference, result.candidate)
            for result in pair_results
        ],
        inputs,
        sorted_products,
    )
    (context.out_dir / "matrix.json").write_text(
        json.dumps(
            {
                "version": PROTOCOL_VERSION,
                "identity": {
                    "algorithm": "sha256",
                    "selection": selection_sha256,
                    "run": run_sha256,
                },
                "selectedCases": list(context.selected),
                "backends": backend_names,
                "inputs": retained_inputs,
                "products": retained_products,
                "pairs": pairs,
                "findings": [finding.to_json() for finding in findings],
                "summary": {
                    "selectedCaseCount": len(context.selected),
                    "backendCount": len(backend_names),
                    "pairCount": len(pair_results),
                    "comparisonCount": sum(
                        len(result.comparisons) for result in pair_results
                    ),
                    "equalComparisonCount": sum(
                        int(comparison["equal"])
                        for result in pair_results
                        for comparison in result.comparisons
                    ),
                    "findingCount": len(findings),
                    "inputCount": len(inputs),
                    "productCount": len(sorted_products),
                },
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )


def verify_evidence_file(
    report_root: Path,
    artifact_name: object,
    expected_sha256: str,
    context: str,
) -> bytes:
    relative = checked_relative_posix_path(artifact_name, context)
    root = report_root.resolve()
    path = root
    for part in PurePosixPath(relative).parts:
        path = path / part
        if path.is_symlink():
            raise ValidationError(f"{context}: evidence path contains a symlink")
    resolved = path.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as error:
        raise ValidationError(f"{context}: evidence path escapes report root") from error
    if not path.is_file():
        raise ValidationError(f"{context}: evidence is not a regular file")
    try:
        content = path.read_bytes()
        actual_sha256 = sha256_bytes(content)
    except OSError as error:
        raise ValidationError(f"{context}: cannot read evidence: {error}") from error
    if actual_sha256 != expected_sha256:
        raise ValidationError(
            f"{context}: SHA-256 mismatch "
            f"(expected {expected_sha256}, got {actual_sha256})"
        )
    return content


def verify_matrix_artifact(path: Path) -> dict:
    """Verify retained inputs, products, comparisons, counts, and identities."""
    if path.is_symlink() or not path.is_file():
        raise ValidationError(f"validation matrix is not a regular file: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot read validation matrix {path}: {error}") from error
    expected_fields = {
        "version",
        "identity",
        "selectedCases",
        "backends",
        "inputs",
        "products",
        "pairs",
        "findings",
        "summary",
    }
    if not isinstance(value, dict) or set(value) != expected_fields:
        raise ValidationError("validation matrix has malformed top-level fields")
    if (
        not isinstance(value["version"], int)
        or isinstance(value["version"], bool)
        or value["version"] != PROTOCOL_VERSION
    ):
        raise ValidationError("validation matrix has unsupported version")
    report_root = path.parent

    selected_cases = value["selectedCases"]
    if (
        not isinstance(selected_cases, list)
        or not selected_cases
        or not all(
            isinstance(case_id, str) and case_id for case_id in selected_cases
        )
        or len(set(selected_cases)) != len(selected_cases)
    ):
        raise ValidationError("validation matrix has malformed selectedCases")

    backend_names = value["backends"]
    if not isinstance(backend_names, list) or not backend_names:
        raise ValidationError("validation matrix has malformed backends")
    checked_backends = [
        validate_backend_name(backend, "validation matrix backend")
        for backend in backend_names
    ]
    if len(set(checked_backends)) != len(checked_backends):
        raise ValidationError("validation matrix has duplicate backends")

    raw_inputs = value["inputs"]
    if not isinstance(raw_inputs, list) or not raw_inputs:
        raise ValidationError("validation matrix has malformed inputs")
    inputs: list[ValidationInput] = []
    for index, item in enumerate(raw_inputs):
        if not isinstance(item, dict) or set(item) != {
            "kind", "name", "sha256", "artifact"
        }:
            raise ValidationError("validation matrix has malformed input")
        kind = validate_backend_name(item["kind"], "validation input kind")
        name = checked_relative_posix_path(item["name"], "validation input name")
        digest = checked_sha256(item["sha256"], "validation input")
        expected_artifact = f"evidence/inputs/{digest}"
        if item["artifact"] != expected_artifact:
            raise ValidationError("validation input has noncanonical artifact path")
        verify_evidence_file(
            report_root,
            item["artifact"],
            digest,
            f"validation input {kind}:{name}",
        )
        if index == 0 and (kind != "corpus" or name != "corpus.json"):
            raise ValidationError("first validation input must be corpus.json")
        inputs.append(ValidationInput(kind, name, digest))
    input_keys = [(item.kind, item.name) for item in inputs]
    if len(set(input_keys)) != len(input_keys):
        raise ValidationError("validation matrix has duplicate inputs")

    raw_products = value["products"]
    if not isinstance(raw_products, list):
        raise ValidationError("validation matrix has malformed products")
    products: list[ValidationProduct] = []
    for item in raw_products:
        if not isinstance(item, dict) or set(item) != {
            "backend", "kind", "name", "sha256", "artifact"
        }:
            raise ValidationError("validation matrix has malformed product")
        backend = validate_backend_name(item["backend"], "validation product backend")
        kind = validate_backend_name(item["kind"], "validation product kind")
        name = checked_relative_posix_path(item["name"], "validation product name")
        digest = checked_sha256(item["sha256"], "validation product")
        if backend not in checked_backends:
            raise ValidationError("validation product names inactive backend")
        expected_artifact = f"evidence/products/{digest}"
        if item["artifact"] != expected_artifact:
            raise ValidationError("validation product has noncanonical artifact path")
        verify_evidence_file(
            report_root,
            item["artifact"],
            digest,
            f"validation product {backend}:{kind}:{name}",
        )
        products.append(ValidationProduct(backend, kind, name, digest))
    product_keys = [
        (product.backend, product.kind, product.name) for product in products
    ]
    if len(set(product_keys)) != len(product_keys):
        raise ValidationError("validation matrix has duplicate products")
    if product_keys != sorted(product_keys):
        raise ValidationError("validation matrix products are not sorted")

    raw_pairs = value["pairs"]
    if not isinstance(raw_pairs, list) or not raw_pairs:
        raise ValidationError("validation matrix has malformed pairs")
    pair_names: list[tuple[str, str]] = []
    comparison_count = 0
    equal_comparison_count = 0
    for item in raw_pairs:
        if not isinstance(item, dict) or set(item) != {
            "reference",
            "candidate",
            "artifact",
            "sha256",
            "comparedCases",
            "equalCases",
            "findingCount",
        }:
            raise ValidationError("validation matrix has malformed pair")
        reference = validate_backend_name(item["reference"], "pair reference")
        candidate = validate_backend_name(item["candidate"], "pair candidate")
        if reference not in checked_backends or candidate not in checked_backends:
            raise ValidationError("validation pair names inactive backend")
        if reference == candidate:
            raise ValidationError("validation pair compares a backend with itself")
        digest = checked_sha256(item["sha256"], "validation comparison")
        expected_artifact = f"evidence/comparisons/{digest}"
        if item["artifact"] != expected_artifact:
            raise ValidationError("validation comparison has noncanonical artifact path")
        comparison_content = verify_evidence_file(
            report_root,
            item["artifact"],
            digest,
            f"validation comparison {reference}:{candidate}",
        )

        counts = []
        for field_name in ("comparedCases", "equalCases", "findingCount"):
            count = item[field_name]
            if not isinstance(count, int) or isinstance(count, bool) or count < 0:
                raise ValidationError(
                    f"validation pair has malformed {field_name}"
                )
            counts.append(count)
        compared_cases, equal_cases, _ = counts
        if equal_cases > compared_cases:
            raise ValidationError("validation pair has too many equal cases")
        try:
            comparison = json.loads(comparison_content.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise ValidationError(
                "validation comparison artifact is not JSON"
            ) from error
        if not isinstance(comparison, dict) or set(comparison) != {
            "version",
            "reference",
            "candidate",
            "comparisons",
            "findings",
            "summary",
        }:
            raise ValidationError("validation comparison artifact is malformed")
        if (
            not isinstance(comparison["version"], int)
            or isinstance(comparison["version"], bool)
            or comparison["version"] != PROTOCOL_VERSION
            or comparison["reference"] != reference
            or comparison["candidate"] != candidate
        ):
            raise ValidationError(
                "validation comparison artifact disagrees with matrix pair"
            )
        comparison_summary = comparison["summary"]
        if (
            not isinstance(comparison["comparisons"], list)
            or not isinstance(comparison["findings"], list)
            or not isinstance(comparison_summary, dict)
            or any(
                not isinstance(count, int)
                or isinstance(count, bool)
                or count < 0
                for count in comparison_summary.values()
            )
            or len(comparison["comparisons"]) != compared_cases
            or len(comparison["findings"]) != item["findingCount"]
        ):
            raise ValidationError("validation comparison artifact is malformed")
        expected_comparison_summary = {
            "selectedCases": len(selected_cases),
            "comparedCases": compared_cases,
            "equalCases": equal_cases,
            "findingCount": item["findingCount"],
        }
        if comparison_summary != expected_comparison_summary:
            raise ValidationError(
                "validation comparison summary disagrees with matrix pair"
            )
        pair_names.append((reference, candidate))
        comparison_count += compared_cases
        equal_comparison_count += equal_cases
    if len(set(pair_names)) != len(pair_names):
        raise ValidationError("validation matrix has duplicate pairs")

    findings = value["findings"]
    if not isinstance(findings, list):
        raise ValidationError("validation matrix has malformed findings")
    for finding in findings:
        if (
            not isinstance(finding, dict)
            or not {"phase", "message"} <= set(finding)
            or set(finding) - {"phase", "message", "backend", "caseId"}
            or not all(isinstance(item, str) for item in finding.values())
        ):
            raise ValidationError("validation matrix has malformed finding")
    summary = value["summary"]
    expected_summary_fields = {
        "selectedCaseCount",
        "backendCount",
        "pairCount",
        "comparisonCount",
        "equalComparisonCount",
        "findingCount",
        "inputCount",
        "productCount",
    }
    if not isinstance(summary, dict) or set(summary) != expected_summary_fields:
        raise ValidationError("validation matrix has malformed summary")
    if any(
        not isinstance(count, int) or isinstance(count, bool) or count < 0
        for count in summary.values()
    ):
        raise ValidationError("validation matrix summary has malformed count")
    expected_summary = {
        "selectedCaseCount": len(selected_cases),
        "backendCount": len(checked_backends),
        "pairCount": len(pair_names),
        "comparisonCount": comparison_count,
        "equalComparisonCount": equal_comparison_count,
        "findingCount": len(findings),
        "inputCount": len(inputs),
        "productCount": len(products),
    }
    if summary != expected_summary:
        raise ValidationError("validation matrix summary disagrees with contents")

    identity = value["identity"]
    if (
        not isinstance(identity, dict)
        or set(identity) != {"algorithm", "selection", "run"}
        or identity["algorithm"] != "sha256"
    ):
        raise ValidationError("validation matrix has malformed identity")
    selection_sha256 = checked_sha256(
        identity["selection"], "validation selection identity"
    )
    run_sha256 = checked_sha256(identity["run"], "validation run identity")
    expected_selection_sha256 = validation_selection_sha256(
        inputs[0].sha256, selected_cases
    )
    if selection_sha256 != expected_selection_sha256:
        raise ValidationError("validation selection identity mismatch")
    expected_run_sha256 = validation_run_sha256(
        selection_sha256,
        checked_backends,
        pair_names,
        tuple(inputs),
        products,
    )
    if run_sha256 != expected_run_sha256:
        raise ValidationError("validation run identity mismatch")
    return value


def validate_matrix(
    context: RunContext,
    pairs: list[tuple[BackendAdapter, BackendAdapter]],
) -> tuple[list[PairValidationResult], list[ValidationFinding]]:
    """Execute each backend once, then compare every requested directed pair."""
    if not pairs:
        raise ValidationError("validation matrix contains no comparison pairs")

    adapters: dict[str, BackendAdapter] = {}
    pair_names: set[tuple[str, str]] = set()
    for reference, candidate in pairs:
        reference_name = validate_backend_name(reference.name, "reference backend")
        candidate_name = validate_backend_name(candidate.name, "candidate backend")
        if reference_name == candidate_name:
            raise ValidationError(
                f"comparison pair must use distinct backends: {reference_name}"
            )
        names = (reference_name, candidate_name)
        if names in pair_names:
            raise ValidationError(
                f"comparison pair selected more than once: "
                f"{reference_name}:{candidate_name}"
            )
        pair_names.add(names)
        for adapter in (reference, candidate):
            existing = adapters.get(adapter.name)
            if existing is not None and existing is not adapter:
                raise ValidationError(
                    f"backend name maps to multiple adapters: {adapter.name}"
                )
            adapters[adapter.name] = adapter

    backend_runs: dict[str, BackendRun] = {}
    backend_findings: dict[str, list[ValidationFinding]] = {}
    all_findings: list[ValidationFinding] = []
    for name, adapter in adapters.items():
        backend_run = adapter.execute(context)
        if backend_run.backend != name:
            raise ValidationError(
                f"adapter {name} returned backend run {backend_run.backend}"
            )
        findings = list(backend_run.findings)
        findings.extend(
            result_domain_findings(
                backend_run.results, name, backend_run.expected_cases
            )
        )
        audit = adapter.audit(context, backend_run)
        findings.extend(audit.findings)
        backend_runs[name] = backend_run
        backend_findings[name] = findings
        all_findings.extend(findings)

        for case_id in context.selected:
            record = backend_run.results.get(case_id)
            if record is not None:
                write_artifact(context.out_dir, case_id, name, record)

    pair_results: list[PairValidationResult] = []
    for reference, candidate in pairs:
        reference_run = backend_runs[reference.name]
        candidate_run = backend_runs[candidate.name]
        comparisons, comparison_findings = compare_backend_results(
            context.descriptor_by_id,
            context.selected,
            reference.name,
            reference_run.results,
            candidate.name,
            candidate_run.results,
            reference_run.blocked_cases | candidate_run.blocked_cases,
        )
        findings = (
            list(backend_findings[reference.name])
            + list(backend_findings[candidate.name])
            + comparison_findings
        )
        all_findings.extend(comparison_findings)
        write_comparison_artifact(
            context.out_dir,
            reference.name,
            candidate.name,
            comparisons,
            findings,
            len(context.selected),
        )
        pair_results.append(
            PairValidationResult(
                reference.name,
                candidate.name,
                comparisons,
                findings,
            )
        )
    products = tuple(
        product
        for backend_run in backend_runs.values()
        for product in backend_run.products
    )
    write_matrix_artifact(
        context, list(adapters), pair_results, all_findings, products
    )
    return pair_results, all_findings


def validate_pair(
    context: RunContext,
    reference: BackendAdapter,
    candidate: BackendAdapter,
) -> tuple[list[dict], list[ValidationFinding]]:
    """Compatibility wrapper for one edge of the validation matrix."""
    pair_results, _ = validate_matrix(context, [(reference, candidate)])
    result = pair_results[0]
    return result.comparisons, result.findings
