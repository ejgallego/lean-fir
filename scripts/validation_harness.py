#!/usr/bin/env python3
"""Compare Lean's native oracle with protocol-compatible candidate backends."""

from __future__ import annotations

import ast
import fcntl
import hashlib
import json
import os
import posixpath
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path, PurePosixPath
from typing import Protocol


PROTOCOL_VERSION = 3
MANIFEST_FIELDS = {
    "version",
    "id",
    "entry",
    "dependencies",
    "args",
    "argSchemas",
    "argumentAliases",
    "nestedArgumentAliases",
    "resultSchema",
    "tags",
    "fuel",
    "provenance",
    "effectProjections",
}
EFFECT_PROJECTION_FIELDS = {"external", "operation", "argSchemas", "resultSchema"}
BACKEND_NAME_CHARACTERS = "abcdefghijklmnopqrstuvwxyz0123456789-_"
RESERVED_PRODUCT_KIND = "product-manifest"
RESERVED_BUILD_INPUT_KIND = "build-input-manifest"
BUILD_INPUT_SCOPE = "reported-loaded"
BUILD_FILE_ACCESS_RECORDER_KIND = "file-access-recorder"
EXECUTION_FILE_ACCESS_RECORDER_KIND = "execution-file-access-recorder"
BUILD_INPUT_REPLAY_ISOLATOR_KIND = "build-input-replay-isolator"
STRACE_OPEN_SYSCALLS = {"open", "openat", "openat2"}
STRACE_EXEC_SYSCALLS = {"execve", "execveat"}
O_ACCMODE = 0x3
O_WRONLY = 0x1
O_PATH = 0x200000
RESERVED_PRODUCT_PATHS = {
    "execution-input.json",
    "stdout.jsonl",
    "stderr.log",
    "build/stdout.jsonl",
    "build/stderr.log",
}


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
class ToolDeclaration:
    kind: str
    name: str
    path: Path | None = None
    command: str | None = None
    resolve_command: tuple[str, ...] | None = None


@dataclass(frozen=True)
class BuildInputDeclaration:
    kind: str
    name: str
    path: Path


@dataclass(frozen=True)
class ValidationBuildInput:
    backend: str
    kind: str
    name: str
    sha256: str
    content: bytes | None = field(default=None, compare=False, repr=False)
    source_path: Path | None = field(default=None, compare=False, repr=False)

    def to_json(self) -> dict[str, str]:
        return {
            "backend": self.backend,
            "kind": self.kind,
            "name": self.name,
            "sha256": self.sha256,
        }


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


@dataclass(frozen=True)
class ProductContract:
    format: str
    target: str
    runtime_flavor: str
    abi: str

    def to_json(self) -> dict[str, str]:
        return {
            "format": self.format,
            "target": self.target,
            "runtimeFlavor": self.runtime_flavor,
            "abi": self.abi,
        }


@dataclass(frozen=True)
class ProductProviderRequirement:
    provider: str
    contract: ProductContract


@dataclass(frozen=True)
class ProductBundle:
    provider: str
    contract: ProductContract
    bundle_sha256: str
    products: tuple[ValidationProduct, ...]
    case_products: tuple[tuple[str, tuple[ValidationProduct, ...]], ...]

    @property
    def products_by_case(self) -> dict[str, tuple[ValidationProduct, ...]]:
        return dict(self.case_products)

    def identity_json(self) -> dict:
        return {
            "version": PROTOCOL_VERSION,
            "provider": self.provider,
            "contract": self.contract.to_json(),
            "products": [product.to_json() for product in self.products],
            "cases": [
                {
                    "caseId": case_id,
                    "products": [product.to_json() for product in products],
                }
                for case_id, products in self.case_products
            ],
        }

    def to_json(self) -> dict:
        return {
            **self.identity_json(),
            "bundleSha256": self.bundle_sha256,
        }


@dataclass(frozen=True)
class ProductConsumer:
    backend: str
    provider: str
    contract: ProductContract
    bundle_sha256: str

    def to_json(self) -> dict:
        return {
            "backend": self.backend,
            "provider": self.provider,
            "contract": self.contract.to_json(),
            "bundleSha256": self.bundle_sha256,
        }


@dataclass(frozen=True)
class ProductReceipt:
    backend: str
    case_id: str
    provider: str
    bundle_sha256: str
    products: tuple[ValidationProduct, ...]

    def to_json(self) -> dict:
        return {
            "backend": self.backend,
            "caseId": self.case_id,
            "provider": self.provider,
            "bundleSha256": self.bundle_sha256,
            "products": [
                {
                    "kind": product.kind,
                    "name": product.name,
                    "sha256": product.sha256,
                }
                for product in self.products
            ],
        }


@dataclass
class ProductProviderRun:
    provider: str
    bundle: ProductBundle
    products: list[ValidationProduct] = field(default_factory=list)
    findings: list[ValidationFinding] = field(default_factory=list)
    tools: list[ValidationTool] = field(default_factory=list)
    build_inputs: list[ValidationBuildInput] = field(default_factory=list)
    artifacts: list[ValidationArtifact] = field(default_factory=list)


@dataclass(frozen=True)
class ValidationTool:
    backend: str
    kind: str
    name: str
    sha256: str
    content: bytes | None = field(default=None, compare=False, repr=False)
    source_path: Path | None = field(default=None, compare=False, repr=False)

    def to_json(self) -> dict[str, str]:
        return {
            "backend": self.backend,
            "kind": self.kind,
            "name": self.name,
            "sha256": self.sha256,
        }


@dataclass(frozen=True)
class ValidationArtifact:
    kind: str
    name: str
    sha256: str
    content: bytes = field(compare=False, repr=False)

    def to_json(self) -> dict[str, str]:
        return {
            "kind": self.kind,
            "name": self.name,
            "sha256": self.sha256,
        }


@dataclass(frozen=True)
class MaterializedExecutionInput:
    path: Path
    identity: tuple[int, int, int, int, int, int]
    artifact: ValidationArtifact

    def verify(self, phase: str) -> None:
        context = f"{self.artifact.name} {phase}"
        if self.path.is_symlink() or not self.path.is_file():
            raise ValidationError(
                f"external execution input is not a regular file {phase}"
            )
        try:
            file_stat = self.path.stat()
            content = regular_file_content_without_symlinks(
                self.path, context
            )
        except OSError as error:
            raise ValidationError(
                f"cannot verify external execution input {phase}: {error}"
            ) from error
        if file_stat.st_nlink != 1:
            raise ValidationError(
                f"external execution input has multiple links {phase}"
            )
        if (file_stat.st_dev, file_stat.st_ino) != self.identity[:2]:
            raise ValidationError(
                f"external execution input was replaced {phase}"
            )
        if content != self.artifact.content:
            raise ValidationError(
                f"external execution input changed {phase}"
            )
        metadata = (
            file_stat.st_dev,
            file_stat.st_ino,
            file_stat.st_ctime_ns,
            file_stat.st_mtime_ns,
            file_stat.st_size,
            file_stat.st_mode & 0o7777,
        )
        if metadata != self.identity:
            raise ValidationError(
                f"external execution input was replaced {phase}"
            )


@dataclass(frozen=True)
class VerifiedEvidence:
    manifest_path: Path
    report_root: Path
    manifest: dict
    matrix: dict


VALIDATION_EVIDENCE_RECEIPT_KIND = "fir-validation-evidence-receipt"
VALIDATION_EVIDENCE_RECEIPT_NAME = "evidence-receipt.json"


def sha256_bytes(content: bytes) -> str:
    return hashlib.sha256(content).hexdigest()


def parse_strace_string(value: str, context: str) -> str:
    try:
        parsed = ast.literal_eval(value)
    except (SyntaxError, ValueError) as error:
        raise ValidationError(f"{context}: malformed strace string") from error
    if not isinstance(parsed, str):
        raise ValidationError(f"{context}: malformed strace string")
    return parsed


def parse_build_file_access_trace(
    content: bytes, context: str
) -> dict[str, tuple[str, ...]]:
    """Decode successful strace file reads and executable acquisitions."""
    try:
        text = content.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValidationError(f"{context}: trace is not UTF-8") from error
    accesses: dict[str, set[str]] = {}

    def record(raw_path: str, access: str) -> None:
        if not os.path.isabs(raw_path):
            raise ValidationError(
                f"{context}: traced {access} path is not absolute: {raw_path}"
            )
        path = os.path.normpath(raw_path)
        accesses.setdefault(path, set()).add(access)

    for line_number, line in enumerate(text.splitlines(), start=1):
        if not line:
            continue
        resumed = re.match(
            r"^\s*\d+\s+<\.\.\. "
            r"(open|openat|openat2|execve|execveat) resumed>",
            line,
        )
        if resumed is not None:
            raise ValidationError(
                f"{context}:{line_number}: resumed traced "
                f"{resumed.group(1)} syscall is ambiguous"
            )
        match = re.match(
            r"^\s*\d+\s+(open|openat|openat2|execve|execveat)\(",
            line,
        )
        if match is None:
            raise ValidationError(
                f"{context}:{line_number}: unrecognized strace line"
            )
        syscall = match.group(1)
        line_context = f"{context}:{line_number}"
        if " = " not in line or line.endswith("<unfinished ...>"):
            raise ValidationError(
                f"{line_context}: incomplete traced {syscall} syscall"
            )
        if syscall in STRACE_OPEN_SYSCALLS:
            result = re.search(
                r" = \d+<(.+)>(?:\(deleted\))?$", line
            )
            if result is None:
                raise ValidationError(
                    f"{line_context}: malformed traced {syscall} result"
                )
            call = line[: result.start()].rstrip()
            flag_match = re.search(
                r"flags=(0x[0-9a-fA-F]+|[0-9]+)", call
            )
            if flag_match is None:
                flag_match = re.search(
                    r",\s*(0x[0-9a-fA-F]+|[0-9]+)"
                    r"(?:,\s*(?:0x[0-9a-fA-F]+|[0-9]+))?\)$",
                    call,
                )
                if flag_match is None:
                    raise ValidationError(
                        f"{line_context}: missing traced {syscall} flags"
                    )
                raw_flag = flag_match.group(1)
            else:
                raw_flag = flag_match.group(1)
            flags = (
                int(raw_flag, 16)
                if raw_flag.lower().startswith("0x")
                else int(raw_flag, 10)
            )
            if flags & O_PATH or flags & O_ACCMODE == O_WRONLY:
                continue
            record(result.group(1), "read")
            continue

        quoted = r'"(?:[^"\\]|\\.)*"'
        if syscall == "execve":
            if re.search(r" = 0$", line) is None:
                raise ValidationError(
                    f"{line_context}: traced execve did not succeed"
                )
            argument = re.search(rf"execve\(({quoted})", line)
            if argument is None:
                raise ValidationError(
                    f"{line_context}: malformed traced execve path"
                )
            record(
                parse_strace_string(argument.group(1), line_context),
                "exec",
            )
            continue

        if re.search(r" = 0$", line) is None:
            raise ValidationError(
                f"{line_context}: traced execveat did not succeed"
            )
        argument = re.search(
            rf"execveat\([^<]*<([^>]+)>,\s*({quoted})", line
        )
        if argument is None:
            raise ValidationError(
                f"{line_context}: malformed traced execveat path"
            )
        base = argument.group(1)
        executable = parse_strace_string(argument.group(2), line_context)
        if os.path.isabs(executable):
            record(executable, "exec")
        elif executable:
            record(os.path.join(base, executable), "exec")
        else:
            record(base, "exec")
    if not accesses:
        raise ValidationError(f"{context}: trace contains no file accesses")
    return {
        path: tuple(sorted(kinds))
        for path, kinds in sorted(accesses.items())
    }


def parse_file_access_trace(
    content: bytes, context: str
) -> dict[str, tuple[str, ...]]:
    """Shared strict parser for build and execution strace evidence."""
    return parse_build_file_access_trace(content, context)


def parse_bwrap_status(content: bytes, context: str) -> tuple[dict, dict]:
    try:
        lines = content.decode("utf-8").splitlines()
        records = [json.loads(line) for line in lines if line]
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"{context}: malformed sandbox status") from error
    namespace_fields = {
        "child-pid",
        "cgroup-namespace",
        "ipc-namespace",
        "mnt-namespace",
        "net-namespace",
        "pid-namespace",
        "uts-namespace",
    }
    if (
        len(records) != 2
        or not isinstance(records[0], dict)
        or set(records[0]) != namespace_fields
        or not all(
            isinstance(value, int)
            and not isinstance(value, bool)
            and value > 0
            for value in records[0].values()
        )
        or records[1] != {"exit-code": 0}
    ):
        raise ValidationError(f"{context}: malformed sandbox status")
    return records[0], records[1]


def canonical_json_bytes(value: object) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=True,
        separators=(",", ":"),
        sort_keys=True,
    ).encode("utf-8")


def execution_input_value(
    backend: str,
    selected_cases: list[str],
    products: tuple[ValidationProduct, ...],
    bundle: ProductBundle | None,
    out_dir: Path,
) -> dict:
    return {
        "version": PROTOCOL_VERSION,
        "backend": backend,
        "selectedCases": list(selected_cases),
        "products": [
            {
                **product.to_json(),
                "path": str(
                    (out_dir / product.backend / product.name).resolve()
                ),
            }
            for product in products
        ],
        "productBundle": bundle.to_json() if bundle is not None else None,
    }


def checked_execution_input(
    content: bytes,
    backend: str,
    selected_cases: list[str],
    products: tuple[ValidationProduct, ...],
    bundle: ProductBundle | None,
    context: str,
    out_dir: Path | None = None,
) -> dict:
    try:
        value = json.loads(content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"{context}: execution input is not JSON"
        ) from error
    if (
        not isinstance(value, dict)
        or set(value)
        != {
            "version",
            "backend",
            "selectedCases",
            "products",
            "productBundle",
        }
        or value["version"] != PROTOCOL_VERSION
        or isinstance(value["version"], bool)
        or value["backend"] != backend
        or value["selectedCases"] != selected_cases
        or not isinstance(value["products"], list)
        or value["productBundle"]
        != (bundle.to_json() if bundle is not None else None)
        or canonical_json_bytes(value) != content
    ):
        raise ValidationError(f"{context}: malformed execution input")
    exposed: list[dict[str, str]] = []
    for index, product in enumerate(value["products"]):
        product_context = f"{context}: product {index}"
        if (
            not isinstance(product, dict)
            or set(product) != {"backend", "kind", "name", "sha256", "path"}
        ):
            raise ValidationError(
                f"{product_context} is malformed"
            )
        product_backend = validate_backend_name(
            product["backend"], f"{product_context} backend"
        )
        product_kind = validate_backend_name(
            product["kind"], f"{product_context} kind"
        )
        product_name = checked_relative_posix_path(
            product["name"], f"{product_context} name"
        )
        product_sha256 = checked_sha256(
            product["sha256"], product_context
        )
        product_path = product["path"]
        if (
            not isinstance(product_path, str)
            or not os.path.isabs(product_path)
            or os.path.normpath(product_path) != product_path
        ):
            raise ValidationError(
                f"{product_context} path is malformed"
            )
        exposed.append(
            {
                "backend": product_backend,
                "kind": product_kind,
                "name": product_name,
                "sha256": product_sha256,
            }
        )
    expected = [product.to_json() for product in products]
    if exposed != expected:
        raise ValidationError(
            f"{context}: products disagree with retained inventory"
        )
    if out_dir is not None:
        expected_paths = [
            str((out_dir / product.backend / product.name).resolve())
            for product in products
        ]
        if [product["path"] for product in value["products"]] != expected_paths:
            raise ValidationError(
                f"{context}: product paths disagree with output inventory"
            )
    return value


def materialize_execution_input(
    out_dir: Path,
    backend: str,
    value: dict,
) -> MaterializedExecutionInput:
    destination = out_dir / backend
    if destination.is_symlink() or not destination.is_dir():
        raise ValidationError(
            f"{backend} output is not a regular directory before execution"
        )
    path = destination / "execution-input.json"
    if path.is_symlink():
        raise ValidationError(
            f"{backend} execution input path is a symlink"
        )
    if path.exists():
        if not path.is_file():
            raise ValidationError(
                f"{backend} execution input path is not a regular file"
            )
        try:
            path.unlink()
        except OSError as error:
            raise ValidationError(
                f"cannot replace {backend} execution input: {error}"
            ) from error
    content = canonical_json_bytes(value)
    descriptor = -1
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags, 0o600)
        remaining = memoryview(content)
        while remaining:
            written = os.write(descriptor, remaining)
            if written <= 0:
                raise OSError("short write")
            remaining = remaining[written:]
        os.fsync(descriptor)
        os.fchmod(descriptor, 0o444)
        file_stat = os.fstat(descriptor)
        if file_stat.st_nlink != 1:
            raise OSError("execution input has multiple links")
    except OSError as error:
        raise ValidationError(
            f"cannot materialize {backend} execution input: {error}"
        ) from error
    finally:
        if descriptor >= 0:
            close_file_descriptor(descriptor)
    artifact = ValidationArtifact(
        "execution-input",
        f"{backend}/execution-input.json",
        sha256_bytes(content),
        content,
    )
    materialized = MaterializedExecutionInput(
        path,
        (
            file_stat.st_dev,
            file_stat.st_ino,
            file_stat.st_ctime_ns,
            file_stat.st_mtime_ns,
            file_stat.st_size,
            file_stat.st_mode & 0o7777,
        ),
        artifact,
    )
    materialized.verify("before execution")
    return materialized


def sealed_snapshot_fd(
    digest: str,
    content: bytes,
    mode: int,
    context: str,
) -> int:
    """Create an immutable in-memory file for one replay overlay."""
    checked_digest = checked_sha256(digest, context)
    if sha256_bytes(content) != checked_digest:
        raise ValidationError(f"{context}: snapshot content digest mismatch")
    if mode not in (0o444, 0o555):
        raise ValidationError(f"{context}: invalid snapshot mode")
    descriptor = -1
    try:
        descriptor = os.memfd_create(
            f"fir-replay-{checked_digest[:16]}",
            os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING,
        )
        remaining = memoryview(content)
        while remaining:
            written = os.write(descriptor, remaining)
            if written <= 0:
                raise OSError("short write to replay snapshot")
            remaining = remaining[written:]
        os.fchmod(descriptor, mode)
        os.utime(descriptor, ns=(0, 0))
        seals = (
            fcntl.F_SEAL_WRITE
            | fcntl.F_SEAL_GROW
            | fcntl.F_SEAL_SHRINK
            | fcntl.F_SEAL_SEAL
        )
        fcntl.fcntl(descriptor, fcntl.F_ADD_SEALS, seals)
        if fcntl.fcntl(descriptor, fcntl.F_GET_SEALS) != seals:
            raise OSError("replay snapshot seals were not applied")
        os.lseek(descriptor, 0, os.SEEK_SET)
        inherited_descriptor = fcntl.fcntl(
            descriptor, fcntl.F_DUPFD_CLOEXEC, 64
        )
        os.close(descriptor)
        descriptor = inherited_descriptor
    except OSError as error:
        if descriptor >= 0:
            os.close(descriptor)
        raise ValidationError(
            f"{context}: cannot seal snapshot blob: {error}"
        ) from error
    return descriptor


def close_file_descriptor(descriptor: int) -> None:
    """Best-effort descriptor cleanup that cannot mask the primary failure."""
    try:
        os.close(descriptor)
    except OSError:
        pass


def canonical_json_sha256(value: object) -> str:
    return sha256_bytes(canonical_json_bytes(value))


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
    tools: list[ValidationTool] | None = None,
    build_inputs: list[ValidationBuildInput] | None = None,
    bundles: list[ProductBundle] | None = None,
    consumers: list[ProductConsumer] | None = None,
    receipts: list[ProductReceipt] | None = None,
) -> str:
    value = {
        "version": PROTOCOL_VERSION,
        "selectionSha256": selection_sha256,
        "backends": backend_names,
        "pairs": [
            {"reference": reference, "candidate": candidate}
            for reference, candidate in pair_names
        ],
        "inputs": [item.to_json() for item in inputs],
        "products": [product.to_json() for product in products],
        "tools": [tool.to_json() for tool in (tools or [])],
        "buildInputs": [
            item.to_json() for item in (build_inputs or [])
        ],
    }
    if bundles is not None or consumers is not None or receipts is not None:
        value["productBundles"] = [
            bundle.to_json() for bundle in (bundles or [])
        ]
        value["productConsumers"] = [
            consumer.to_json() for consumer in (consumers or [])
        ]
        value["productReceipts"] = [
            receipt.to_json() for receipt in (receipts or [])
        ]
    return canonical_json_sha256(value)


def validation_evidence_sha256(
    run_sha256: str, matrix_sha256: str
) -> str:
    return canonical_json_sha256(
        {
            "version": PROTOCOL_VERSION,
            "runSha256": checked_sha256(
                run_sha256, "validation evidence run"
            ),
            "matrixSha256": checked_sha256(
                matrix_sha256, "validation evidence matrix"
            ),
        }
    )


def validation_evidence_manifest_path(
    out_dir: Path, run_sha256: str, matrix_sha256: str
) -> Path:
    run_digest = checked_sha256(run_sha256, "validation evidence run")
    matrix_digest = checked_sha256(
        matrix_sha256, "validation evidence matrix"
    )
    evidence_digest = validation_evidence_sha256(run_digest, matrix_digest)
    return (
        out_dir
        / "evidence"
        / "runs"
        / run_digest
        / f"{evidence_digest}.json"
    )


def validation_evidence_receipt_value(source: VerifiedEvidence) -> dict:
    report_root = source.report_root.resolve()
    try:
        manifest = source.manifest_path.resolve().relative_to(report_root)
    except ValueError as error:
        raise ValidationError(
            "validation evidence receipt manifest escapes its report root"
        ) from error
    identity = source.manifest["identity"]
    matrix = source.manifest["matrix"]
    provisional = {
        "version": PROTOCOL_VERSION,
        "kind": VALIDATION_EVIDENCE_RECEIPT_KIND,
        "source": {
            "runSha256": checked_sha256(
                identity["run"], "validation evidence receipt run"
            ),
            "evidenceSha256": checked_sha256(
                identity["evidence"], "validation evidence receipt evidence"
            ),
            "matrixSha256": checked_sha256(
                matrix["sha256"], "validation evidence receipt matrix"
            ),
        },
        "manifest": checked_relative_posix_path(
            manifest.as_posix(), "validation evidence receipt manifest"
        ),
    }
    return {
        **provisional,
        "identity": {
            "algorithm": "sha256",
            "receipt": canonical_json_sha256(provisional),
        },
    }


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


def checked_config_relative_posix_path(value: object, context: str) -> str:
    if (
        not isinstance(value, str)
        or not value
        or "\\" in value
        or PurePosixPath(value).is_absolute()
        or posixpath.normpath(value) != value
        or value == ".."
    ):
        raise ValidationError(
            f"{context}: path must be a normalized config-relative POSIX path"
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


def product_contract_from_json(value: object, context: str) -> ProductContract:
    if not isinstance(value, dict) or set(value) != {
        "format", "target", "runtimeFlavor", "abi"
    }:
        raise ValidationError(
            f"{context}: product contract must contain format, target, "
            "runtimeFlavor, and abi"
        )
    fields = []
    for name in ("format", "target", "runtimeFlavor", "abi"):
        field_value = value[name]
        if not isinstance(field_value, str) or not field_value:
            raise ValidationError(
                f"{context}: product contract {name} must be a nonempty string"
            )
        fields.append(field_value)
    return ProductContract(fields[0], fields[1], fields[2], fields[3])


def product_bundle_sha256(
    provider: str,
    contract: ProductContract,
    products: tuple[ValidationProduct, ...],
    case_products: tuple[tuple[str, tuple[ValidationProduct, ...]], ...],
) -> str:
    provisional = ProductBundle(
        validate_backend_name(provider, "product provider"),
        contract,
        "0" * 64,
        products,
        case_products,
    )
    return canonical_json_sha256(provisional.identity_json())


def validation_product_and_content_from_file(
    backend: str,
    declaration: ProductDeclaration,
    out_dir: Path,
) -> tuple[ValidationProduct, bytes]:
    backend_name = validate_backend_name(backend)
    kind = validate_backend_name(declaration.kind, f"{backend_name} product kind")
    product_path = checked_relative_posix_path(
        declaration.path, f"{backend_name} product"
    )
    backend_root = out_dir.resolve() / backend_name
    if backend_root.is_symlink() or not backend_root.is_dir():
        raise ValidationError(
            f"{backend_name} product root is not a regular directory"
        )
    path = backend_root.joinpath(*PurePosixPath(product_path).parts)
    parent = backend_root
    for part in PurePosixPath(product_path).parts[:-1]:
        parent = parent / part
        if parent.is_symlink() or not parent.is_dir():
            raise ValidationError(
                f"{backend_name} product path contains a symlink or "
                f"non-directory parent: {product_path}"
            )
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
    return (
        ValidationProduct(
            backend_name,
            kind,
            product_path,
            sha256_bytes(content),
        ),
        content,
    )


def validation_product_from_file(
    backend: str,
    declaration: ProductDeclaration,
    out_dir: Path,
) -> ValidationProduct:
    return validation_product_and_content_from_file(
        backend, declaration, out_dir
    )[0]


def product_declarations_from_manifest(
    content: bytes, context: str
) -> tuple[ProductDeclaration, ...]:
    try:
        value = json.loads(content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"{context}: cannot parse product manifest: {error}"
        ) from error
    if not isinstance(value, dict) or set(value) not in (
        {"version", "products"},
        {"version", "contract", "products", "cases"},
    ):
        raise ValidationError(
            f"{context}: product manifest must contain version and products, "
            "optionally with contract and cases"
        )
    version = value["version"]
    if (
        not isinstance(version, int)
        or isinstance(version, bool)
        or version != PROTOCOL_VERSION
    ):
        raise ValidationError(
            f"{context}: product manifest has unsupported version"
        )
    products = value["products"]
    if not isinstance(products, list) or not products:
        raise ValidationError(
            f"{context}: product manifest products must be a nonempty array"
        )
    declarations: list[ProductDeclaration] = []
    paths: set[str] = set()
    for index, product in enumerate(products):
        product_context = f"{context}/products/{index}"
        if not isinstance(product, dict) or set(product) != {"kind", "path"}:
            raise ValidationError(
                f"{product_context}: expected kind and path fields"
            )
        kind = validate_backend_name(product["kind"], product_context)
        path = checked_relative_posix_path(product["path"], product_context)
        if kind == RESERVED_PRODUCT_KIND:
            raise ValidationError(
                f"{product_context}: product kind is reserved"
            )
        if path in RESERVED_PRODUCT_PATHS:
            raise ValidationError(
                f"{product_context}: product path is reserved by the harness"
            )
        if path in paths:
            raise ValidationError(
                f"{context}: duplicate product path: {path}"
            )
        paths.add(path)
        declarations.append(ProductDeclaration(kind, path))
    return tuple(
        sorted(
            declarations,
            key=lambda declaration: (declaration.kind, declaration.path),
        )
    )


def product_bundle_from_manifest(
    provider: str,
    configured_contract: ProductContract,
    content: bytes,
    products: tuple[ValidationProduct, ...],
    selected_cases: list[str],
    context: str,
) -> ProductBundle:
    try:
        value = json.loads(content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"{context}: cannot parse product bundle manifest: {error}"
        ) from error
    if not isinstance(value, dict) or set(value) != {
        "version", "contract", "products", "cases"
    }:
        raise ValidationError(
            f"{context}: product bundle manifest must contain version, "
            "contract, products, and cases"
        )
    if (
        not isinstance(value["version"], int)
        or isinstance(value["version"], bool)
        or value["version"] != PROTOCOL_VERSION
    ):
        raise ValidationError(f"{context}: unsupported product bundle version")
    contract = product_contract_from_json(value["contract"], f"{context}/contract")
    if contract != configured_contract:
        raise ValidationError(
            f"{context}: emitted product contract disagrees with provider config"
        )
    declarations = product_declarations_from_manifest(content, context)
    declaration_keys = [(item.kind, item.path) for item in declarations]
    raw_declaration_keys = [
        (item.get("kind"), item.get("path"))
        for item in value["products"]
        if isinstance(item, dict)
    ]
    if raw_declaration_keys != declaration_keys:
        raise ValidationError(f"{context}: products are not sorted")

    provider_name = validate_backend_name(provider, "product provider")
    ordinary_products = tuple(
        product for product in products
        if product.kind != RESERVED_PRODUCT_KIND
    )
    if any(product.backend != provider_name for product in ordinary_products):
        raise ValidationError(f"{context}: product owner disagrees with provider")
    product_by_key = {
        (product.kind, product.name): product for product in ordinary_products
    }
    if len(product_by_key) != len(ordinary_products):
        raise ValidationError(f"{context}: duplicate provider products")
    if set(declaration_keys) != set(product_by_key):
        raise ValidationError(
            f"{context}: manifest declarations disagree with provider products"
        )

    raw_cases = value["cases"]
    if not isinstance(raw_cases, list):
        raise ValidationError(f"{context}: cases must be an object array")
    bindings: list[tuple[str, tuple[ValidationProduct, ...]]] = []
    seen_cases: set[str] = set()
    referenced: set[tuple[str, str]] = set()
    for index, raw_case in enumerate(raw_cases):
        case_context = f"{context}/cases/{index}"
        if not isinstance(raw_case, dict) or set(raw_case) != {
            "caseId", "products"
        }:
            raise ValidationError(
                f"{case_context}: expected caseId and products fields"
            )
        case_id = validate_backend_name(raw_case["caseId"], case_context)
        if case_id in seen_cases:
            raise ValidationError(f"{context}: duplicate case binding: {case_id}")
        seen_cases.add(case_id)
        raw_references = raw_case["products"]
        if not isinstance(raw_references, list) or not raw_references:
            raise ValidationError(
                f"{case_context}: products must be a nonempty object array"
            )
        keys: list[tuple[str, str]] = []
        for reference_index, raw_reference in enumerate(raw_references):
            reference_context = (
                f"{case_context}/products/{reference_index}"
            )
            if not isinstance(raw_reference, dict) or set(raw_reference) != {
                "kind", "path"
            }:
                raise ValidationError(
                    f"{reference_context}: expected kind and path fields"
                )
            key = (
                validate_backend_name(raw_reference["kind"], reference_context),
                checked_relative_posix_path(
                    raw_reference["path"], reference_context
                ),
            )
            if key not in product_by_key:
                raise ValidationError(
                    f"{reference_context}: references an undeclared product"
                )
            keys.append(key)
        if len(set(keys)) != len(keys) or keys != sorted(keys):
            raise ValidationError(
                f"{case_context}: product references must be sorted and unique"
            )
        referenced.update(keys)
        bindings.append(
            (case_id, tuple(product_by_key[key] for key in keys))
        )
    expected_cases = list(selected_cases)
    if [case_id for case_id, _ in bindings] != sorted(expected_cases):
        raise ValidationError(
            f"{context}: case bindings must exactly match selected cases in "
            "sorted order"
        )
    if referenced != set(product_by_key):
        raise ValidationError(f"{context}: contains unreferenced products")
    sorted_products = tuple(
        sorted(ordinary_products, key=lambda item: (item.kind, item.name))
    )
    case_products = tuple(bindings)
    digest = product_bundle_sha256(
        provider_name, contract, sorted_products, case_products
    )
    return ProductBundle(
        provider_name,
        contract,
        digest,
        sorted_products,
        case_products,
    )


def product_bundle_from_json(
    value: object,
    provider_names: list[str],
    matrix_products: list[ValidationProduct],
    selected_cases: list[str],
    context: str,
) -> ProductBundle:
    if not isinstance(value, dict) or set(value) != {
        "version",
        "provider",
        "contract",
        "bundleSha256",
        "products",
        "cases",
    }:
        raise ValidationError(f"{context}: malformed product bundle")
    if (
        not isinstance(value["version"], int)
        or isinstance(value["version"], bool)
        or value["version"] != PROTOCOL_VERSION
    ):
        raise ValidationError(f"{context}: unsupported product bundle version")
    provider = validate_backend_name(value["provider"], f"{context} provider")
    if provider not in provider_names:
        raise ValidationError(f"{context}: names inactive provider")
    contract = product_contract_from_json(value["contract"], f"{context} contract")
    digest = checked_sha256(value["bundleSha256"], f"{context} identity")
    available = {
        (product.backend, product.kind, product.name, product.sha256): product
        for product in matrix_products
        if product.backend == provider
        and product.kind != RESERVED_PRODUCT_KIND
    }

    def checked_reference(raw: object, reference_context: str) -> ValidationProduct:
        if not isinstance(raw, dict) or set(raw) != {
            "backend", "kind", "name", "sha256"
        }:
            raise ValidationError(
                f"{reference_context}: malformed product reference"
            )
        key = (
            validate_backend_name(raw["backend"], f"{reference_context} owner"),
            validate_backend_name(raw["kind"], f"{reference_context} kind"),
            checked_relative_posix_path(raw["name"], f"{reference_context} name"),
            checked_sha256(raw["sha256"], reference_context),
        )
        product = available.get(key)
        if product is None:
            raise ValidationError(
                f"{reference_context}: references an undeclared provider product"
            )
        return product

    raw_products = value["products"]
    if not isinstance(raw_products, list) or not raw_products:
        raise ValidationError(f"{context}: products must be a nonempty array")
    products = tuple(
        checked_reference(item, f"{context}/products/{index}")
        for index, item in enumerate(raw_products)
    )
    product_keys = [(item.kind, item.name) for item in products]
    if len(set(product_keys)) != len(product_keys) or product_keys != sorted(
        product_keys
    ):
        raise ValidationError(f"{context}: products are not sorted and unique")
    if set(products) != set(available.values()):
        raise ValidationError(
            f"{context}: inventory disagrees with retained provider products"
        )
    raw_cases = value["cases"]
    if not isinstance(raw_cases, list):
        raise ValidationError(f"{context}: cases must be an object array")
    case_products: list[tuple[str, tuple[ValidationProduct, ...]]] = []
    referenced: set[ValidationProduct] = set()
    for index, raw_case in enumerate(raw_cases):
        case_context = f"{context}/cases/{index}"
        if not isinstance(raw_case, dict) or set(raw_case) != {
            "caseId", "products"
        }:
            raise ValidationError(f"{case_context}: malformed case binding")
        case_id = validate_backend_name(raw_case["caseId"], case_context)
        raw_references = raw_case["products"]
        if not isinstance(raw_references, list) or not raw_references:
            raise ValidationError(
                f"{case_context}: products must be a nonempty array"
            )
        bound = tuple(
            checked_reference(item, f"{case_context}/products/{item_index}")
            for item_index, item in enumerate(raw_references)
        )
        bound_keys = [(item.kind, item.name) for item in bound]
        if len(set(bound_keys)) != len(bound_keys) or bound_keys != sorted(
            bound_keys
        ):
            raise ValidationError(
                f"{case_context}: products are not sorted and unique"
            )
        referenced.update(bound)
        case_products.append((case_id, bound))
    if [case_id for case_id, _ in case_products] != sorted(selected_cases):
        raise ValidationError(
            f"{context}: case bindings do not match selected cases"
        )
    if referenced != set(products):
        raise ValidationError(f"{context}: contains unreferenced products")
    checked_cases = tuple(case_products)
    expected_digest = product_bundle_sha256(
        provider, contract, products, checked_cases
    )
    if digest != expected_digest:
        raise ValidationError(f"{context}: product bundle identity mismatch")
    return ProductBundle(
        provider, contract, digest, products, checked_cases
    )


def build_input_declarations_from_manifest(
    content: bytes, context: str
) -> tuple[BuildInputDeclaration, ...]:
    try:
        value = json.loads(content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"{context}: cannot parse build input manifest: {error}"
        ) from error
    if not isinstance(value, dict) or set(value) != {
        "version", "scope", "inputs"
    }:
        raise ValidationError(
            f"{context}: build input manifest must contain version, scope, "
            "and inputs"
        )
    version = value["version"]
    if (
        not isinstance(version, int)
        or isinstance(version, bool)
        or version != PROTOCOL_VERSION
    ):
        raise ValidationError(
            f"{context}: build input manifest has unsupported version"
        )
    if value["scope"] != BUILD_INPUT_SCOPE:
        raise ValidationError(
            f"{context}: build input manifest has unsupported scope"
        )
    raw_inputs = value["inputs"]
    if not isinstance(raw_inputs, list) or not raw_inputs:
        raise ValidationError(
            f"{context}: build input manifest inputs must be a nonempty array"
        )
    declarations: list[BuildInputDeclaration] = []
    identities: set[tuple[str, str]] = set()
    sources: set[str] = set()
    for index, item in enumerate(raw_inputs):
        item_context = f"{context}/inputs/{index}"
        if not isinstance(item, dict) or set(item) != {
            "kind", "name", "path"
        }:
            raise ValidationError(
                f"{item_context}: expected kind, name, and path fields"
            )
        kind = validate_backend_name(item["kind"], item_context)
        if kind == RESERVED_BUILD_INPUT_KIND:
            raise ValidationError(
                f"{item_context}: build input kind is reserved"
            )
        name = checked_relative_posix_path(item["name"], item_context)
        raw_path = item["path"]
        if (
            not isinstance(raw_path, str)
            or not raw_path
            or "\x00" in raw_path
            or not Path(raw_path).is_absolute()
        ):
            raise ValidationError(
                f"{item_context}: path must be an absolute filesystem path"
            )
        path = Path(os.path.abspath(raw_path))
        identity = (kind, name)
        if identity in identities:
            raise ValidationError(
                f"{context}: duplicate build input: {kind}:{name}"
            )
        identities.add(identity)
        source = str(path)
        if source in sources:
            raise ValidationError(
                f"{context}: duplicate build input path: {source}"
            )
        sources.add(source)
        declarations.append(BuildInputDeclaration(kind, name, path))
    return tuple(
        sorted(
            declarations,
            key=lambda declaration: (declaration.kind, declaration.name),
        )
    )


def regular_file_content_without_symlinks(path: Path, context: str) -> bytes:
    absolute = Path(os.path.abspath(path))
    current = Path(absolute.anchor)
    for part in absolute.parts[1:]:
        current = current / part
        if current.is_symlink():
            raise ValidationError(f"{context}: path contains a symlink")
    if not absolute.is_file():
        raise ValidationError(f"{context}: path is not a regular file")
    try:
        return absolute.read_bytes()
    except OSError as error:
        raise ValidationError(f"{context}: cannot read file: {error}") from error


def validation_build_input_from_file(
    backend: str, declaration: BuildInputDeclaration
) -> ValidationBuildInput:
    backend_name = validate_backend_name(
        backend, "validation build input backend"
    )
    kind = validate_backend_name(
        declaration.kind, "validation build input kind"
    )
    name = checked_relative_posix_path(
        declaration.name, "validation build input name"
    )
    context = f"validation build input {backend_name}:{kind}:{name}"
    content = regular_file_content_without_symlinks(
        declaration.path, context
    )
    return ValidationBuildInput(
        backend_name,
        kind,
        name,
        sha256_bytes(content),
        content,
        Path(os.path.abspath(declaration.path)),
    )


def canonical_build_input_manifest_bytes(
    build_inputs: tuple[ValidationBuildInput, ...]
) -> bytes:
    value = {
        "version": PROTOCOL_VERSION,
        "scope": BUILD_INPUT_SCOPE,
        "inputs": [
            {
                "kind": item.kind,
                "name": item.name,
                "sha256": item.sha256,
            }
            for item in sorted(
                build_inputs, key=lambda item: (item.kind, item.name)
            )
        ],
    }
    return canonical_json_bytes(value)


def build_inputs_from_canonical_manifest(
    backend: str, content: bytes, context: str
) -> tuple[ValidationBuildInput, ...]:
    try:
        value = json.loads(content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"{context}: cannot parse canonical build input manifest: {error}"
        ) from error
    if not isinstance(value, dict) or set(value) != {
        "version", "scope", "inputs"
    }:
        raise ValidationError(
            f"{context}: malformed canonical build input manifest"
        )
    if (
        value["version"] != PROTOCOL_VERSION
        or isinstance(value["version"], bool)
        or value["scope"] != BUILD_INPUT_SCOPE
        or not isinstance(value["inputs"], list)
        or not value["inputs"]
    ):
        raise ValidationError(
            f"{context}: malformed canonical build input manifest"
        )
    inputs: list[ValidationBuildInput] = []
    for index, item in enumerate(value["inputs"]):
        item_context = f"{context}/inputs/{index}"
        if not isinstance(item, dict) or set(item) != {
            "kind", "name", "sha256"
        }:
            raise ValidationError(
                f"{item_context}: expected kind, name, and sha256 fields"
            )
        kind = validate_backend_name(item["kind"], item_context)
        if kind == RESERVED_BUILD_INPUT_KIND:
            raise ValidationError(
                f"{item_context}: build input kind is reserved"
            )
        name = checked_relative_posix_path(item["name"], item_context)
        digest = checked_sha256(item["sha256"], item_context)
        inputs.append(ValidationBuildInput(backend, kind, name, digest))
    keys = [(item.kind, item.name) for item in inputs]
    if len(set(keys)) != len(keys) or keys != sorted(keys):
        raise ValidationError(
            f"{context}: canonical build inputs are duplicate or unsorted"
        )
    return tuple(inputs)


def validation_tool_from_file(
    backend: str,
    kind: str,
    name: str,
    path: Path,
) -> ValidationTool:
    backend_name = validate_backend_name(backend, "validation tool backend")
    checked_kind = validate_backend_name(kind, "validation tool kind")
    checked_name = checked_relative_posix_path(name, "validation tool name")
    if path.is_symlink() or not path.is_file():
        raise ValidationError(f"validation tool is not a regular file: {path}")
    try:
        content = path.read_bytes()
    except OSError as error:
        raise ValidationError(f"cannot hash validation tool {path}: {error}") from error
    return ValidationTool(
        backend_name,
        checked_kind,
        checked_name,
        sha256_bytes(content),
        content,
        path.resolve(),
    )


def validation_tool_from_declaration(
    backend: str,
    declaration: ToolDeclaration,
    root: Path | None = None,
) -> ValidationTool:
    if (declaration.path is None) == (declaration.command is None):
        raise ValidationError("validation tool must declare one path or command")
    if declaration.path is not None:
        if declaration.resolve_command is not None:
            raise ValidationError(
                "path validation tool cannot declare a resolver command"
            )
        path = declaration.path
    else:
        command = declaration.command
        if command is None:
            raise ValidationError("validation tool command is missing")
        if declaration.resolve_command is None:
            resolved = shutil.which(command)
            if resolved is None:
                raise ValidationError(
                    f"cannot resolve validation tool command: {command}"
                )
            path = Path(resolved).resolve()
        else:
            if root is None:
                raise ValidationError(
                    f"validation tool resolver requires a root: {command}"
                )
            completed = run(list(declaration.resolve_command), root)
            resolved_paths = [
                line.strip()
                for line in completed.stdout.splitlines()
                if line.strip()
            ]
            if completed.returncode != 0 or len(resolved_paths) != 1:
                raise ValidationError(
                    f"cannot resolve validation tool command with "
                    f"{' '.join(declaration.resolve_command)}: {command}"
                )
            path = Path(resolved_paths[0])
            if not path.is_absolute():
                raise ValidationError(
                    f"validation tool resolver returned a relative path: "
                    f"{command}"
                )
            path = Path(os.path.abspath(path))
    return validation_tool_from_file(
        backend,
        declaration.kind,
        declaration.name,
        path,
    )


def resolve_lake_command(root: Path, command: str) -> Path:
    completed = run(["lake", "env", "which", command], root)
    paths = [line.strip() for line in completed.stdout.splitlines() if line.strip()]
    if completed.returncode != 0 or len(paths) != 1:
        raise ValidationError(f"cannot resolve Lake command: {command}")
    path = Path(paths[0])
    if not path.is_absolute():
        raise ValidationError(f"Lake resolved a relative command path: {command}")
    return path


def run(
    command: list[str],
    cwd: Path,
    timeout: int = 120,
    extra_env: dict[str, str] | None = None,
    pass_fds: tuple[int, ...] = (),
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
            pass_fds=pass_fds,
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


def _argument_path_key(path: object, context: str) -> tuple[int, ...]:
    if (
        not isinstance(path, dict)
        or set(path) != {"argument", "children"}
        or not isinstance(path["argument"], int)
        or isinstance(path["argument"], bool)
        or path["argument"] < 0
        or not isinstance(path["children"], list)
        or not path["children"]
        or not all(
            isinstance(child, int) and not isinstance(child, bool) and child >= 0
            for child in path["children"]
        )
    ):
        raise ValidationError(f"{context}: malformed nested argument path")
    return (path["argument"], *path["children"])


def _resolve_argument_path(
    arg_schemas: list[object], args: list[object], path: object, context: str
) -> tuple[object, object]:
    key = _argument_path_key(path, context)
    argument = key[0]
    if argument >= len(args):
        raise ValidationError(f"{context}: argument {argument} is out of bounds")
    schema = arg_schemas[argument]
    datum = args[argument]
    for child in key[1:]:
        if isinstance(schema, dict) and set(schema) == {"seq"}:
            sequence_schema = schema["seq"]
            sequence_datum = datum.get("seq") if isinstance(datum, dict) else None
            if (
                not isinstance(sequence_schema, dict)
                or set(sequence_schema) != {"element"}
                or not isinstance(sequence_datum, dict)
                or set(sequence_datum) != {"value"}
                or not isinstance(sequence_datum["value"], list)
                or child >= len(sequence_datum["value"])
            ):
                raise ValidationError(f"{context}: invalid sequence child {child}")
            schema = sequence_schema["element"]
            datum = sequence_datum["value"][child]
            continue
        if isinstance(schema, dict) and set(schema) == {"ctor"}:
            constructor_schema = schema["ctor"]
            constructor_datum = datum.get("ctor") if isinstance(datum, dict) else None
            if (
                not isinstance(constructor_schema, dict)
                or not isinstance(constructor_schema.get("fields"), list)
                or not isinstance(constructor_datum, dict)
                or not isinstance(constructor_datum.get("fields"), list)
                or child >= len(constructor_schema["fields"])
                or child >= len(constructor_datum["fields"])
            ):
                raise ValidationError(f"{context}: invalid constructor child {child}")
            schema = constructor_schema["fields"][child]
            datum = constructor_datum["fields"][child]
            continue
        raise ValidationError(f"{context}: child {child} descends through a non-container")
    return schema, datum


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

        case_id = validate_backend_name(
            value["id"], f"native corpus manifest line {line_number} case ID"
        )
        entry = value["entry"]
        version = value["version"]
        dependencies = value["dependencies"]
        args = value["args"]
        arg_schemas = value["argSchemas"]
        argument_aliases = value["argumentAliases"]
        nested_argument_aliases = value["nestedArgumentAliases"]
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
        if not isinstance(argument_aliases, list):
            raise ValidationError(
                f"native corpus manifest/{case_id}: malformed argumentAliases"
            )
        alias_targets: set[int] = set()
        last_alias_target = -1
        for alias in argument_aliases:
            if (
                not isinstance(alias, dict)
                or set(alias) != {"source", "target"}
                or not isinstance(alias["source"], int)
                or isinstance(alias["source"], bool)
                or not isinstance(alias["target"], int)
                or isinstance(alias["target"], bool)
            ):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: malformed argumentAliases"
                )
            source = alias["source"]
            target = alias["target"]
            if source < 0 or source >= target or target >= len(args):
                raise ValidationError(
                    f"native corpus manifest/{case_id}: argument alias "
                    f"{source}->{target} is out of canonical bounds"
                )
            if target <= last_alias_target:
                raise ValidationError(
                    f"native corpus manifest/{case_id}: argument alias targets "
                    "must be strictly increasing"
                )
            if source in alias_targets:
                raise ValidationError(
                    f"native corpus manifest/{case_id}: argument alias source "
                    f"{source} is not an independently materialized root"
                )
            if arg_schemas[source] != arg_schemas[target]:
                raise ValidationError(
                    f"native corpus manifest/{case_id}: argument alias "
                    f"{source}->{target} connects different schemas"
                )
            if args[source] != args[target]:
                raise ValidationError(
                    f"native corpus manifest/{case_id}: argument alias "
                    f"{source}->{target} connects different fixtures"
                )
            alias_targets.add(target)
            last_alias_target = target
        if not isinstance(nested_argument_aliases, list):
            raise ValidationError(
                f"native corpus manifest/{case_id}: malformed nestedArgumentAliases"
            )
        root_alias_targets = {alias["target"] for alias in argument_aliases}
        nested_alias_targets: set[tuple[int, ...]] = set()
        last_nested_target: tuple[int, ...] | None = None
        for alias in nested_argument_aliases:
            if not isinstance(alias, dict) or set(alias) != {"source", "target"}:
                raise ValidationError(
                    f"native corpus manifest/{case_id}: malformed nestedArgumentAliases"
                )
            context = f"native corpus manifest/{case_id}"
            source_key = _argument_path_key(alias["source"], context)
            target_key = _argument_path_key(alias["target"], context)
            if source_key[0] in root_alias_targets or target_key[0] in root_alias_targets:
                raise ValidationError(
                    f"{context}: nested argument alias descends below a top-level alias target"
                )
            if source_key >= target_key:
                raise ValidationError(
                    f"{context}: nested argument alias source must precede target"
                )
            if last_nested_target is not None and last_nested_target >= target_key:
                raise ValidationError(
                    f"{context}: nested argument alias targets must be strictly increasing"
                )
            if source_key in nested_alias_targets:
                raise ValidationError(
                    f"{context}: nested argument alias source is not independently materialized"
                )
            source_schema, source_datum = _resolve_argument_path(
                arg_schemas, args, alias["source"], f"{context} source"
            )
            target_schema, target_datum = _resolve_argument_path(
                arg_schemas, args, alias["target"], f"{context} target"
            )
            if source_schema != target_schema:
                raise ValidationError(
                    f"{context}: nested argument alias connects different schemas"
                )
            if source_datum != target_datum:
                raise ValidationError(
                    f"{context}: nested argument alias connects different fixtures"
                )
            nested_alias_targets.add(target_key)
            last_nested_target = target_key
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
    descriptors: list[dict],
    requested: list[str] | None,
    tag: str | None,
    exclude_tags: tuple[str, ...] = (),
) -> list[str]:
    all_cases = [descriptor["id"] for descriptor in descriptors]
    known = set(all_cases)
    excluded = {
        descriptor["id"]
        for descriptor in descriptors
        if any(exclude_tag in descriptor["tags"] for exclude_tag in exclude_tags)
    }
    if requested:
        duplicates = sorted({case_id for case_id in requested if requested.count(case_id) > 1})
        if duplicates:
            raise ValidationError(
                f"validation case selected more than once: {', '.join(duplicates)}"
            )
        unknown = sorted(set(requested) - known)
        if unknown:
            raise ValidationError(f"unknown validation case(s): {', '.join(unknown)}")
        explicitly_excluded = sorted(set(requested) & excluded)
        if explicitly_excluded:
            raise ValidationError(
                "validation case(s) excluded by plan tag: "
                + ", ".join(explicitly_excluded)
            )
        return requested
    if tag:
        selected = [
            descriptor["id"]
            for descriptor in descriptors
            if tag in descriptor["tags"] and descriptor["id"] not in excluded
        ]
        if not selected:
            raise ValidationError(f"corpus tag selected no cases: {tag}")
        return selected
    selected = [case_id for case_id in all_cases if case_id not in excluded]
    if not selected:
        raise ValidationError("validation plan exclusion tags selected no cases")
    return selected


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


def retain_evidence_bundle(
    out_dir: Path,
    run_sha256: str,
    evidence_sha256: str,
    content: bytes,
) -> str:
    """Publish one immutable matrix under its run and evidence identities."""
    run_digest = checked_sha256(run_sha256, "validation bundle run")
    evidence_digest = checked_sha256(
        evidence_sha256, "validation bundle evidence"
    )
    root = out_dir.resolve()
    directory = root
    for part in ("evidence", "runs", run_digest):
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
    bundle = directory / f"{evidence_digest}.json"
    if bundle.is_symlink() or (bundle.exists() and not bundle.is_file()):
        raise ValidationError(
            f"validation evidence bundle is not a regular file: {bundle}"
        )
    if bundle.exists():
        try:
            existing = bundle.read_bytes()
        except OSError as error:
            raise ValidationError(
                f"cannot read validation evidence bundle {bundle}: {error}"
            ) from error
        if existing != content:
            raise ValidationError(
                f"validation evidence bundle disagrees with its identity: "
                f"{evidence_digest}"
            )
    else:
        temporary_path: Path | None = None
        try:
            with tempfile.NamedTemporaryFile(
                dir=directory,
                prefix=".validation-bundle-",
                delete=False,
            ) as temporary:
                temporary.write(content)
                temporary.flush()
                os.fsync(temporary.fileno())
                temporary_path = Path(temporary.name)
            os.link(temporary_path, bundle)
        except FileExistsError:
            try:
                existing = bundle.read_bytes()
            except OSError as error:
                raise ValidationError(
                    f"cannot read concurrently retained validation evidence "
                    f"bundle {bundle}: {error}"
                ) from error
            if existing != content:
                raise ValidationError(
                    f"validation evidence bundle disagrees with its identity: "
                    f"{evidence_digest}"
                )
        except OSError as error:
            raise ValidationError(
                f"cannot retain validation evidence bundle {bundle}: {error}"
            ) from error
        finally:
            if temporary_path is not None:
                try:
                    temporary_path.unlink(missing_ok=True)
                except OSError as error:
                    raise ValidationError(
                        f"cannot remove temporary validation bundle "
                        f"{temporary_path}: {error}"
                    ) from error
    return bundle.relative_to(root).as_posix()


def write_evidence_manifest(
    out_dir: Path,
    matrix_content: bytes,
    run_sha256: str,
) -> Path:
    try:
        matrix_value = json.loads(matrix_content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"cannot retain non-JSON validation matrix: {error}"
        ) from error
    if not isinstance(matrix_value, dict) or not isinstance(
        matrix_value.get("coverage"), dict
    ):
        raise ValidationError("validation matrix has no retainable coverage")
    run_digest = checked_sha256(run_sha256, "validation evidence run")
    matrix_digest = sha256_bytes(matrix_content)
    matrix_artifact = retain_evidence_blob(
        out_dir, "matrices", matrix_digest, matrix_content
    )
    evidence_digest = validation_evidence_sha256(run_digest, matrix_digest)
    manifest_content = (
        json.dumps(
            {
                "version": PROTOCOL_VERSION,
                "identity": {
                    "algorithm": "sha256",
                    "run": run_digest,
                    "evidence": evidence_digest,
                },
                "matrix": {
                    "sha256": matrix_digest,
                    "artifact": matrix_artifact,
                },
                "coverage": matrix_value["coverage"],
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")
    relative = retain_evidence_bundle(
        out_dir,
        run_digest,
        evidence_digest,
        manifest_content,
    )
    return out_dir / relative


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


def retain_validation_tools(
    context: RunContext,
    tools: list[ValidationTool],
) -> list[dict[str, str]]:
    retained: list[dict[str, str]] = []
    for tool in tools:
        if tool.source_path is None or tool.content is None:
            raise ValidationError(
                f"validation tool has no retainable source: "
                f"{tool.backend}:{tool.kind}:{tool.name}"
            )
        captured = validation_tool_from_file(
            tool.backend,
            tool.kind,
            tool.name,
            tool.source_path,
        )
        if captured != tool:
            raise ValidationError(
                f"validation tool changed before evidence retention: "
                f"{tool.backend}:{tool.kind}:{tool.name}"
            )
        retained.append(
            {
                **tool.to_json(),
                "artifact": retain_evidence_blob(
                    context.out_dir, "tools", tool.sha256, tool.content
                ),
            }
        )
    return retained


def retain_validation_build_inputs(
    context: RunContext,
    build_inputs: list[ValidationBuildInput],
) -> list[dict[str, str]]:
    retained: list[dict[str, str]] = []
    for item in build_inputs:
        if item.content is None:
            raise ValidationError(
                f"validation build input has no retainable content: "
                f"{item.backend}:{item.kind}:{item.name}"
            )
        if item.source_path is not None:
            captured = validation_build_input_from_file(
                item.backend,
                BuildInputDeclaration(
                    item.kind, item.name, item.source_path
                ),
            )
            if captured != item:
                raise ValidationError(
                    f"validation build input changed before evidence "
                    f"retention: {item.backend}:{item.kind}:{item.name}"
                )
        elif item.kind != RESERVED_BUILD_INPUT_KIND:
            raise ValidationError(
                f"validation build input has no retainable source: "
                f"{item.backend}:{item.kind}:{item.name}"
            )
        retained.append(
            {
                **item.to_json(),
                "artifact": retain_evidence_blob(
                    context.out_dir,
                    "build-inputs",
                    item.sha256,
                    item.content,
                ),
            }
        )
    return retained


VALIDATION_ARTIFACT_KINDS = {
    "backend-result",
    "build-determinism",
    "build-file-access",
    "build-file-access-trace",
    "build-input-replay",
    "build-input-replay-manifest",
    "build-input-replay-status",
    "build-input-replay-trace",
    "execution-file-access",
    "execution-file-access-trace",
    "execution-input",
    "process-stdout",
    "process-stderr",
}


def is_build_attempt_scope(scope: str) -> bool:
    return scope == "build" or (
        scope.startswith("build-")
        and scope[6:].isdigit()
        and int(scope[6:]) >= 2
    )


def validation_artifact_scope(
    kind: object,
    name: object,
    backend_names: list[str],
    selected_cases: list[str],
) -> tuple[str, str | None, str]:
    checked_kind = validate_backend_name(kind, "validation artifact kind")
    checked_name = checked_relative_posix_path(
        name, "validation artifact name"
    )
    if checked_kind not in VALIDATION_ARTIFACT_KINDS:
        raise ValidationError(
            f"unsupported validation artifact kind: {checked_kind}"
        )
    parts = PurePosixPath(checked_name).parts
    case_id: str | None = None
    if checked_kind == "build-input-replay":
        if len(parts) != 2 or parts[1] != "build-input-replay.json":
            raise ValidationError(
                "build-input-replay artifact has noncanonical name"
            )
        backend, scope = parts[0], "build-input-replay"
    elif checked_kind == "build-input-replay-manifest":
        if (
            len(parts) != 3
            or parts[1] != "build-input-replay"
            or parts[2] != "build-input-manifest.json"
        ):
            raise ValidationError(
                "build-input-replay-manifest artifact has noncanonical name"
            )
        backend, scope = parts[0], "build-input-replay"
    elif checked_kind == "build-input-replay-status":
        if (
            len(parts) != 3
            or parts[1] != "build-input-replay"
            or parts[2] != "sandbox-status.jsonl"
        ):
            raise ValidationError(
                "build-input-replay-status artifact has noncanonical name"
            )
        backend, scope = parts[0], "build-input-replay"
    elif checked_kind == "build-input-replay-trace":
        if (
            len(parts) != 3
            or parts[1] != "build-input-replay"
            or parts[2] != "file-access.strace"
        ):
            raise ValidationError(
                "build-input-replay-trace artifact has noncanonical name"
            )
        backend, scope = parts[0], "build-input-replay"
    elif checked_kind == "build-file-access":
        if len(parts) != 2 or parts[1] != "build-file-access.json":
            raise ValidationError(
                "build-file-access artifact has noncanonical name"
            )
        backend, scope = parts[0], "build-file-access"
    elif checked_kind == "build-file-access-trace":
        if (
            len(parts) != 3
            or parts[2] != "file-access.strace"
            or not is_build_attempt_scope(parts[1])
        ):
            raise ValidationError(
                "build-file-access-trace artifact has noncanonical name"
            )
        backend, scope = parts[0], parts[1]
    elif checked_kind == "execution-file-access":
        if len(parts) != 2 or parts[1] != "execution-file-access.json":
            raise ValidationError(
                "execution-file-access artifact has noncanonical name"
            )
        backend, scope = parts[0], "execution-file-access"
    elif checked_kind == "execution-file-access-trace":
        if (
            len(parts) != 3
            or parts[1] != "execute"
            or parts[2] != "file-access.strace"
        ):
            raise ValidationError(
                "execution-file-access-trace artifact has noncanonical name"
            )
        backend, scope = parts[0], "execute"
    elif checked_kind == "execution-input":
        if len(parts) != 2 or parts[1] != "execution-input.json":
            raise ValidationError(
                "execution-input artifact has noncanonical name"
            )
        backend, scope = parts[0], "execute"
    elif checked_kind == "build-determinism":
        if len(parts) != 2 or parts[1] != "build-determinism.json":
            raise ValidationError(
                "build-determinism artifact has noncanonical name"
            )
        backend, scope = parts[0], "build-determinism"
    elif checked_kind == "backend-result":
        if len(parts) != 3 or parts[2] != "result.json":
            raise ValidationError("backend-result artifact has noncanonical name")
        case_id, backend, scope = parts[0], parts[1], "result"
    else:
        suffix = (
            "stdout.jsonl"
            if checked_kind == "process-stdout"
            else "stderr.log"
        )
        if parts[-1] != suffix:
            raise ValidationError(
                f"{checked_kind} artifact has noncanonical name"
            )
        if len(parts) == 2:
            backend, scope = parts[0], "execute"
        elif len(parts) == 3 and (
            is_build_attempt_scope(parts[1])
            or parts[1] == "build-input-replay"
        ):
            backend, scope = parts[0], parts[1]
        elif len(parts) == 3:
            case_id, backend, scope = parts[0], parts[1], "execute"
        else:
            raise ValidationError(
                f"{checked_kind} artifact has noncanonical name"
            )
    validate_backend_name(backend, "validation artifact backend")
    if backend not in backend_names:
        raise ValidationError("validation artifact names inactive backend")
    if case_id is not None:
        validate_backend_name(case_id, "validation artifact case ID")
        if case_id not in selected_cases:
            raise ValidationError("validation artifact names unselected case")
    return backend, case_id, scope


def retain_validation_artifacts(
    context: RunContext,
    artifacts: list[ValidationArtifact],
) -> list[dict[str, str]]:
    retained: list[dict[str, str]] = []
    for artifact in artifacts:
        digest = checked_sha256(artifact.sha256, "validation artifact")
        if sha256_bytes(artifact.content) != digest:
            raise ValidationError(
                f"validation artifact content disagrees with SHA-256: "
                f"{artifact.kind}:{artifact.name}"
            )
        retained.append(
            {
                **artifact.to_json(),
                "artifact": retain_evidence_blob(
                    context.out_dir,
                    "artifacts",
                    digest,
                    artifact.content,
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

def write_artifact(
    out_dir: Path, case_id: str, backend: str, record: dict
) -> ValidationArtifact:
    checked_case_id = validate_backend_name(case_id, "validation case ID")
    checked_backend = validate_backend_name(backend, "validation backend")
    destination = out_dir / checked_case_id / checked_backend
    destination.mkdir(parents=True, exist_ok=True)
    content = (json.dumps(record, indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )
    (destination / "result.json").write_bytes(content)
    return ValidationArtifact(
        "backend-result",
        f"{checked_case_id}/{checked_backend}/result.json",
        sha256_bytes(content),
        content,
    )


def write_process_artifacts(
    destination: Path,
    completed: subprocess.CompletedProcess[str],
    artifact_prefix: str,
) -> tuple[ValidationArtifact, ValidationArtifact]:
    prefix = checked_relative_posix_path(
        artifact_prefix, "validation process artifact prefix"
    )
    destination.mkdir(parents=True, exist_ok=True)
    stdout = completed.stdout.encode("utf-8")
    stderr = completed.stderr.encode("utf-8")
    (destination / "stdout.jsonl").write_bytes(stdout)
    (destination / "stderr.log").write_bytes(stderr)
    return (
        ValidationArtifact(
            "process-stdout",
            f"{prefix}/stdout.jsonl",
            sha256_bytes(stdout),
            stdout,
        ),
        ValidationArtifact(
            "process-stderr",
            f"{prefix}/stderr.log",
            sha256_bytes(stderr),
            stderr,
        ),
    )


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
    run_context: RunContext | None = None


@dataclass(frozen=True)
class RunContext:
    root: Path
    out_dir: Path
    descriptors: list[dict]
    selected: list[str]
    inputs: tuple[ValidationInput, ...] = ()
    product_bundles: dict[str, ProductBundle] = field(default_factory=dict)

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
    tools: list[ValidationTool] = field(default_factory=list)
    build_inputs: list[ValidationBuildInput] = field(default_factory=list)
    artifacts: list[ValidationArtifact] = field(default_factory=list)


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


PRODUCT_BUNDLE_RECEIPT_DIAGNOSTIC = "validation-product-bundle"


def product_bundle_receipt_value(
    bundle: ProductBundle, case_id: str
) -> str:
    products = bundle.products_by_case.get(case_id)
    if products is None:
        raise ValidationError(
            f"product bundle {bundle.provider} has no binding for {case_id}"
        )
    return json.dumps(
        {
            "provider": bundle.provider,
            "bundleSha256": bundle.bundle_sha256,
            "products": [
                {
                    "kind": product.kind,
                    "name": product.name,
                    "sha256": product.sha256,
                }
                for product in products
            ],
        },
        separators=(",", ":"),
        sort_keys=True,
    )


def checked_product_bundle_receipt(
    record: dict,
    backend: str,
    case_id: str,
    bundle: ProductBundle,
) -> ProductReceipt:
    diagnostics = record.get("diagnostics", [])
    if not isinstance(diagnostics, list) or not all(
        isinstance(item, dict) for item in diagnostics
    ):
        raise ValidationError(
            f"{backend}/{case_id}: malformed diagnostics while reading "
            "product bundle receipt"
        )
    receipts = [
        item for item in diagnostics
        if item.get("key") == PRODUCT_BUNDLE_RECEIPT_DIAGNOSTIC
    ]
    if len(receipts) != 1 or set(receipts[0]) != {"key", "value"}:
        raise ValidationError(
            f"{backend}/{case_id}: missing or malformed product bundle receipt"
        )
    expected = product_bundle_receipt_value(bundle, case_id)
    try:
        actual = json.dumps(
            json.loads(receipts[0]["value"]),
            separators=(",", ":"),
            sort_keys=True,
        )
    except (TypeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"{backend}/{case_id}: malformed product bundle receipt"
        ) from error
    if actual != expected:
        raise ValidationError(
            f"{backend}/{case_id}: product receipt disagrees with provider "
            "case binding"
        )
    products = bundle.products_by_case.get(case_id)
    if products is None:
        raise ValidationError(
            f"{backend}/{case_id}: provider has no case binding"
        )
    return ProductReceipt(
        backend,
        case_id,
        bundle.provider,
        bundle.bundle_sha256,
        products,
    )


def product_bundle_receipt_findings(
    backend_run: BackendRun, bundle: ProductBundle
) -> list[ValidationFinding]:
    findings: list[ValidationFinding] = []
    for case_id, record in sorted(backend_run.results.items()):
        try:
            checked_product_bundle_receipt(
                record, backend_run.backend, case_id, bundle
            )
        except ValidationError as error:
            message = str(error)
            prefix = f"{backend_run.backend}/{case_id}: "
            if message.startswith(prefix):
                message = message[len(prefix):]
            findings.append(
                ValidationFinding(
                    "audit", message, backend_run.backend, case_id
                )
            )
    return findings


def verify_product_bundle_files(
    context: RunContext, bundle: ProductBundle, phase: str
) -> None:
    for product in bundle.products:
        captured = validation_product_from_file(
            bundle.provider,
            ProductDeclaration(product.kind, product.name),
            context.out_dir,
        )
        if captured != product:
            raise ValidationError(
                f"{bundle.provider} bundle product changed {phase}: "
                f"{product.kind}:{product.name}"
            )


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


class ProductProvider(Protocol):
    name: str

    def build(self, context: BuildContext) -> ProductProviderRun:
        ...


@dataclass
class ExternalCommandAdapter:
    """Protocol adapter driven by shell-free commands from a JSON config."""

    name: str
    run_command: list[str]
    result_domain: str
    build_command: list[str] = field(default_factory=list)
    build_replay_command: list[str] = field(default_factory=list)
    timeout_seconds: int = 120
    product_declarations: tuple[ProductDeclaration, ...] = ()
    product_manifest: str | None = None
    build_input_manifest: str | None = None
    build_file_access_recorder: ToolDeclaration | None = None
    execution_file_access_recorder: ToolDeclaration | None = None
    build_input_replay_isolator: ToolDeclaration | None = None
    build_attempts: int = 1
    tool_declarations: tuple[ToolDeclaration, ...] = ()
    build_tool_declarations: tuple[ToolDeclaration, ...] = ()
    product_provider: ProductProviderRequirement | None = None
    _built_products: tuple[ValidationProduct, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_tools: tuple[ValidationTool, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_build_tools: tuple[ValidationTool, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_build_file_access_recorder: ValidationTool | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_execution_file_access_recorder: ValidationTool | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_build_input_replay_isolator: ValidationTool | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_build_inputs: tuple[ValidationBuildInput, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_build_command: tuple[str, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_build_replay_command: tuple[str, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _built_run_command: tuple[str, ...] | None = field(
        default=None, init=False, repr=False, compare=False
    )
    _build_artifacts: tuple[ValidationArtifact, ...] = field(
        default=(), init=False, repr=False, compare=False
    )
    _build_findings: tuple[ValidationFinding, ...] = field(
        default=(), init=False, repr=False, compare=False
    )

    def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
        return descriptors

    def environment(
        self, out_dir: Path, run_context: RunContext | None = None
    ) -> dict[str, str]:
        environment = {
            "FIR_VALIDATION_BACKEND": self.name,
            "FIR_VALIDATION_OUT_DIR": str((out_dir / self.name).resolve()),
            "FIR_VALIDATION_PROTOCOL_VERSION": str(PROTOCOL_VERSION),
        }
        if run_context is not None:
            environment.update(
                {
                    "FIR_VALIDATION_CASES": json.dumps(
                        run_context.selected, separators=(",", ":")
                    ),
                    "FIR_VALIDATION_CORPUS": str(
                        (run_context.out_dir / "corpus.json").resolve()
                    ),
                }
            )
        return environment

    def verify_corpus(self, context: RunContext, phase: str) -> None:
        path = context.out_dir / "corpus.json"
        if path.is_symlink() or not path.is_file():
            raise ValidationError(
                f"{self.name} validation corpus is not a regular file {phase}"
            )
        expected = corpus_artifact_bytes(context.descriptors)
        try:
            actual = path.read_bytes()
        except OSError as error:
            raise ValidationError(
                f"cannot read {self.name} validation corpus {phase}: {error}"
            ) from error
        if actual != expected:
            raise ValidationError(
                f"{self.name} validation corpus changed {phase}"
            )

    def tool_environment_value(
        self, tools: tuple[ValidationTool, ...]
    ) -> str:
        return json.dumps(
            [
                {
                    **tool.to_json(),
                    "path": str(tool.source_path),
                }
                for tool in tools
            ],
            separators=(",", ":"),
            sort_keys=True,
        )

    def collect_products(self, out_dir: Path) -> tuple[ValidationProduct, ...]:
        declarations = self.product_declarations
        products: list[ValidationProduct] = []
        if self.product_manifest is not None:
            manifest_declaration = ProductDeclaration(
                RESERVED_PRODUCT_KIND, self.product_manifest
            )
            manifest_product, content = validation_product_and_content_from_file(
                self.name, manifest_declaration, out_dir
            )
            declarations = product_declarations_from_manifest(
                content, f"{self.name} product manifest"
            )
            if any(
                declaration.path == self.product_manifest
                for declaration in declarations
            ):
                raise ValidationError(
                    f"{self.name} product manifest cannot declare itself"
                )
            if self.build_input_manifest is not None and any(
                declaration.path == self.build_input_manifest
                for declaration in declarations
            ):
                raise ValidationError(
                    f"{self.name} product manifest cannot declare its "
                    "build input manifest"
                )
            products.append(manifest_product)
        products.extend(
            validation_product_from_file(self.name, declaration, out_dir)
            for declaration in sorted(
                declarations,
                key=lambda item: (item.kind, item.path),
            )
        )
        return tuple(
            sorted(products, key=lambda item: (item.kind, item.name))
        )

    def collect_build_inputs(
        self, out_dir: Path
    ) -> tuple[ValidationBuildInput, ...]:
        if self.build_input_manifest is None:
            return ()
        declaration = ProductDeclaration(
            RESERVED_BUILD_INPUT_KIND, self.build_input_manifest
        )
        _, content = validation_product_and_content_from_file(
            self.name, declaration, out_dir
        )
        declarations = build_input_declarations_from_manifest(
            content, f"{self.name} build input manifest"
        )
        members = tuple(
            validation_build_input_from_file(self.name, item)
            for item in declarations
        )
        canonical = canonical_build_input_manifest_bytes(members)
        manifest = ValidationBuildInput(
            self.name,
            RESERVED_BUILD_INPUT_KIND,
            self.build_input_manifest,
            sha256_bytes(canonical),
            canonical,
        )
        return tuple(
            sorted(
                (*members, manifest),
                key=lambda item: (item.kind, item.name),
            )
        )

    def collect_tools(
        self,
        root: Path,
        declarations: tuple[ToolDeclaration, ...],
    ) -> tuple[ValidationTool, ...]:
        return tuple(
            validation_tool_from_declaration(self.name, declaration, root)
            for declaration in sorted(
                declarations,
                key=lambda item: (item.kind, item.name),
            )
        )

    def bind_command(
        self,
        root: Path,
        command: list[str],
        declarations: tuple[ToolDeclaration, ...],
        tools: tuple[ValidationTool, ...],
        phase: str,
    ) -> tuple[str, ...]:
        """Replace declared tool arguments with the exact captured files."""
        if not declarations:
            return tuple(command)
        ordered_declarations = sorted(
            declarations, key=lambda item: (item.kind, item.name)
        )
        bound = list(command)
        pairs = list(zip(ordered_declarations, tools, strict=True))
        command_pairs = [
            pair for pair in pairs if pair[0].command is not None
        ]
        if len(command_pairs) != 1:
            raise ValidationError(
                f"{self.name} {phase} must declare exactly one command tool"
            )
        command_declaration, command_tool = command_pairs[0]
        if bound[0] != command_declaration.command:
            raise ValidationError(
                f"{self.name} command tool does not match {phase}Command[0]"
            )
        if command_tool.source_path is None:
            raise ValidationError(f"{self.name} command tool has no source path")
        bound[0] = str(command_tool.source_path)

        for declaration, tool in pairs:
            if declaration.path is None:
                continue
            matches = [
                index
                for index, argument in enumerate(bound[1:], start=1)
                if Path(
                    os.path.abspath(
                        Path(argument)
                        if Path(argument).is_absolute()
                        else root / argument
                    )
                )
                == declaration.path
            ]
            if len(matches) != 1:
                raise ValidationError(
                    f"{self.name} path tool {declaration.kind}:"
                    f"{declaration.name} must match exactly one "
                    f"{phase}Command argument"
                )
            if tool.source_path is None:
                raise ValidationError(
                    f"{self.name} path tool {declaration.kind}:"
                    f"{declaration.name} has no source path"
                )
            bound[matches[0]] = str(tool.source_path)
        return tuple(bound)

    def verify_captured_tools(
        self, tools: tuple[ValidationTool, ...], phase: str
    ) -> None:
        for tool in tools:
            if tool.source_path is None:
                raise ValidationError(
                    f"{self.name} tool {tool.kind}:{tool.name} has no source path"
                )
            try:
                current = validation_tool_from_file(
                    self.name,
                    tool.kind,
                    tool.name,
                    tool.source_path,
                )
            except ValidationError as error:
                raise ValidationError(
                    f"{self.name} tools changed {phase}"
                ) from error
            if current != tool:
                raise ValidationError(f"{self.name} tools changed {phase}")

    def remove_stale_products(self, out_dir: Path) -> None:
        backend_root = (out_dir / self.name).resolve()
        declarations = list(self.product_declarations)
        if self.build_input_manifest is not None:
            declarations.append(
                ProductDeclaration(
                    RESERVED_BUILD_INPUT_KIND, self.build_input_manifest
                )
            )
        for declaration in declarations:
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

    def clear_dynamic_product_staging(self, out_dir: Path) -> None:
        backend_root = out_dir.resolve() / self.name
        if backend_root.is_symlink() or (
            backend_root.exists() and not backend_root.is_dir()
        ):
            raise ValidationError(
                f"{self.name} output path is not a regular directory"
            )
        if backend_root.exists():
            try:
                shutil.rmtree(backend_root)
            except OSError as error:
                raise ValidationError(
                    f"cannot clear {self.name} product staging: {error}"
                ) from error

    def run_build_attempt(
        self,
        context: BuildContext,
        attempt: int,
        destination: Path,
        artifact_prefix: str,
        environment: dict[str, str],
    ) -> tuple[
        subprocess.CompletedProcess[str],
        tuple[ValidationArtifact, ...],
        tuple[dict[str, object], dict[str, tuple[str, ...]]] | None,
    ]:
        command = list(self._built_build_command or ())
        trace_path: Path | None = None
        trace_identity: tuple[int, int] | None = None
        trace_name: str | None = None
        recorder = self._built_build_file_access_recorder
        if recorder is not None:
            if recorder.source_path is None:
                raise ValidationError(
                    f"{self.name} build file-access recorder has no source path"
                )
            trace_root = context.out_dir.resolve() / "build-file-access-traces"
            if trace_root.is_symlink() or (
                trace_root.exists() and not trace_root.is_dir()
            ):
                raise ValidationError(
                    f"{self.name} build file-access trace root is not a directory"
                )
            trace_root.mkdir(parents=True, exist_ok=True)
            try:
                trace_fd, raw_trace_path = tempfile.mkstemp(
                    prefix=f"{self.name}-{attempt}-",
                    suffix=".strace",
                    dir=trace_root,
                )
            except OSError as error:
                raise ValidationError(
                    f"cannot create {self.name} build file-access trace: "
                    f"{error}"
                ) from error
            try:
                trace_stat = os.fstat(trace_fd)
            except OSError as error:
                raise ValidationError(
                    f"cannot identify {self.name} build file-access trace: "
                    f"{error}"
                ) from error
            finally:
                os.close(trace_fd)
            trace_path = Path(raw_trace_path)
            trace_identity = (trace_stat.st_dev, trace_stat.st_ino)
            build_scope = "build" if attempt == 1 else f"build-{attempt}"
            trace_name = f"{self.name}/{build_scope}/file-access.strace"
            command = [
                str(recorder.source_path),
                "-f",
                "-qq",
                "--kill-on-exit",
                "-s",
                "0",
                "-yy",
                "-X",
                "raw",
                "-e",
                "trace=open,openat,openat2,execve,execveat",
                "-e",
                "status=successful",
                "-e",
                "signal=none",
                "-o",
                str(trace_path),
                "--",
                *command,
            ]
        completed = run(
            command,
            context.root,
            self.timeout_seconds,
            environment,
        )
        artifacts = write_process_artifacts(
            destination, completed, artifact_prefix
        )
        if recorder is None or completed.returncode != 0:
            return completed, artifacts, None
        if (
            trace_path is None
            or trace_name is None
            or trace_identity is None
        ):
            raise ValidationError(
                f"{self.name} build file-access recorder lost its trace path"
            )
        if trace_path.is_symlink() or not trace_path.is_file():
            raise ValidationError(
                f"{self.name} build file-access recorder produced no trace"
            )
        try:
            trace_stat = trace_path.stat()
        except OSError as error:
            raise ValidationError(
                f"cannot stat {self.name} build file-access trace: {error}"
            ) from error
        if (trace_stat.st_dev, trace_stat.st_ino) != trace_identity:
            raise ValidationError(
                f"{self.name} build file-access trace was replaced"
            )
        try:
            trace_content = trace_path.read_bytes()
        except OSError as error:
            raise ValidationError(
                f"cannot read {self.name} build file-access trace: {error}"
            ) from error
        trace_sha256 = sha256_bytes(trace_content)
        accesses = parse_build_file_access_trace(
            trace_content,
            f"{self.name} build file-access trace attempt {attempt}",
        )
        trace_artifact = ValidationArtifact(
            "build-file-access-trace",
            trace_name,
            trace_sha256,
            trace_content,
        )
        trace_record: dict[str, object] = {
            "attempt": attempt,
            "trace": {
                "name": trace_name,
                "sha256": trace_sha256,
            },
            "accesses": [
                {"path": path, "accesses": list(kinds)}
                for path, kinds in accesses.items()
            ],
            "accessCount": len(accesses),
        }
        return completed, (*artifacts, trace_artifact), (
            trace_record,
            accesses,
        )

    def bind_reported_inputs_to_file_accesses(
        self,
        attempt: int | str,
        trace_record: dict[str, object],
        accesses: dict[str, tuple[str, ...]],
        build_inputs: tuple[ValidationBuildInput, ...],
    ) -> dict[str, object]:
        reported_inputs: list[dict[str, object]] = []
        missing: list[str] = []
        for item in build_inputs:
            if item.source_path is None:
                continue
            path = os.path.normpath(str(item.source_path.resolve()))
            observed = accesses.get(path)
            if observed is None:
                missing.append(f"{item.kind}:{item.name}")
                continue
            reported_inputs.append(
                {
                    **item.to_json(),
                    "path": path,
                    "accesses": list(observed),
                }
            )
        if missing:
            raise ValidationError(
                f"{self.name} reported build inputs were not observed by "
                f"the file-access recorder on attempt {attempt}: "
                + ", ".join(missing)
            )
        return {
            **trace_record,
            "reportedInputs": reported_inputs,
            "reportedInputCount": len(reported_inputs),
        }

    def run_build_input_replay(
        self,
        context: BuildContext,
        source_accesses: dict[str, tuple[str, ...]],
    ) -> tuple[tuple[ValidationArtifact, ...], tuple[ValidationFinding, ...]]:
        isolator = self._built_build_input_replay_isolator
        recorder = self._built_build_file_access_recorder
        if (
            isolator is None
            or recorder is None
            or isolator.source_path is None
            or recorder.source_path is None
            or self._built_products is None
            or self._built_build_inputs is None
            or self._built_build_command is None
            or self._built_build_replay_command is None
            or self._built_build_tools is None
        ):
            raise ValidationError(
                f"{self.name} build-input replay is not initialized"
            )
        replay_parent = (
            context.out_dir.resolve() / "build-input-replay-output"
        )
        replay_backend = replay_parent / self.name
        if replay_backend.is_symlink() or (
            replay_backend.exists() and not replay_backend.is_dir()
        ):
            raise ValidationError(
                f"{self.name} build-input replay output is not a directory"
            )
        if replay_backend.exists():
            try:
                shutil.rmtree(replay_backend)
            except OSError as error:
                raise ValidationError(
                    f"cannot clear {self.name} build-input replay output: "
                    f"{error}"
                ) from error
        replay_backend.mkdir(parents=True, exist_ok=True)

        bindings: list[dict[str, object]] = []
        overlay_specs: list[tuple[str, bytes, str, int, str]] = []
        binding_targets: set[str] = set()

        def add_binding(
            category: str,
            kind: str,
            name: str,
            digest: str,
            content: bytes,
            target_path: Path,
            blob_category: str,
            required_accesses: tuple[str, ...] | None = None,
        ) -> None:
            target = os.path.normpath(str(target_path.resolve()))
            if any(
                target == root or target.startswith(f"{root}/")
                for root in ("/dev", "/proc", "/tmp")
            ):
                raise ValidationError(
                    f"{self.name} replay binding is beneath an isolated "
                    f"runtime path: {target}"
                )
            if target == str(replay_backend) or target.startswith(
                f"{replay_backend}/"
            ):
                raise ValidationError(
                    f"{self.name} replay binding collides with replay output"
                )
            if target in binding_targets:
                raise ValidationError(
                    f"{self.name} replay has duplicate binding target: "
                    f"{target}"
                )
            binding_targets.add(target)
            accesses = source_accesses.get(target, ())
            if required_accesses is not None and accesses != required_accesses:
                raise ValidationError(
                    f"{self.name} replay source accesses changed for "
                    f"{kind}:{name}"
                )
            if required_accesses is not None and not accesses:
                raise ValidationError(
                    f"{self.name} replay source was not observed: "
                    f"{kind}:{name}"
                )
            mode = 0o555 if "exec" in accesses else 0o444
            overlay_specs.append(
                (
                    digest,
                    content,
                    target,
                    mode,
                    f"{self.name} replay binding {category}:{kind}:{name}",
                )
            )
            bindings.append(
                {
                    "backend": self.name,
                    "category": category,
                    "kind": kind,
                    "name": name,
                    "sha256": digest,
                    "path": target,
                    "mode": mode,
                    "accesses": list(accesses),
                    "blob": f"evidence/{blob_category}/{digest}",
                }
            )

        for item in self._built_build_inputs:
            if item.kind == RESERVED_BUILD_INPUT_KIND:
                continue
            if item.content is None or item.source_path is None:
                raise ValidationError(
                    f"{self.name} replay input has no captured source: "
                    f"{item.kind}:{item.name}"
                )
            current = validation_build_input_from_file(
                self.name,
                BuildInputDeclaration(
                    item.kind, item.name, item.source_path
                ),
            )
            if current != item:
                raise ValidationError(
                    f"{self.name} build inputs changed before replay"
                )
            target = os.path.normpath(str(item.source_path.resolve()))
            input_accesses = source_accesses.get(target, ())
            add_binding(
                "build-input",
                item.kind,
                item.name,
                item.sha256,
                item.content,
                item.source_path,
                "build-inputs",
                input_accesses,
            )
        if not any(
            binding["category"] == "build-input"
            for binding in bindings
        ):
            raise ValidationError(
                f"{self.name} build-input replay has no input members"
            )
        for tool in self._built_build_tools:
            if tool.kind in {
                BUILD_FILE_ACCESS_RECORDER_KIND,
                BUILD_INPUT_REPLAY_ISOLATOR_KIND,
            }:
                continue
            if tool.content is None or tool.source_path is None:
                raise ValidationError(
                    f"{self.name} replay tool has no captured source: "
                    f"{tool.kind}:{tool.name}"
                )
            tool_target = os.path.normpath(str(tool.source_path.resolve()))
            tool_accesses = source_accesses.get(tool_target, ())
            add_binding(
                "build-tool",
                tool.kind,
                tool.name,
                tool.sha256,
                tool.content,
                tool.source_path,
                "tools",
                tool_accesses,
            )
        if context.run_context is not None:
            corpus_path = context.run_context.out_dir / "corpus.json"
            corpus_content = corpus_artifact_bytes(
                context.run_context.descriptors
            )
            add_binding(
                "validation-input",
                "corpus",
                "corpus.json",
                sha256_bytes(corpus_content),
                corpus_content,
                corpus_path,
                "inputs",
            )
        ordered_overlays = sorted(
            zip(bindings, overlay_specs, strict=True),
            key=lambda item: (
                str(item[0]["category"]),
                str(item[0]["kind"]),
                str(item[0]["name"]),
            ),
        )
        bindings = [item[0] for item in ordered_overlays]
        overlay_specs = [item[1] for item in ordered_overlays]

        trace_root = context.out_dir.resolve() / "build-file-access-traces"
        if trace_root.is_symlink() or (
            trace_root.exists() and not trace_root.is_dir()
        ):
            raise ValidationError(
                f"{self.name} replay trace root is not a directory"
            )
        trace_root.mkdir(parents=True, exist_ok=True)
        try:
            trace_fd, raw_trace_path = tempfile.mkstemp(
                prefix=f"{self.name}-replay-",
                suffix=".strace",
                dir=trace_root,
            )
            trace_stat = os.fstat(trace_fd)
            os.close(trace_fd)
        except OSError as error:
            raise ValidationError(
                f"cannot create {self.name} replay trace: {error}"
            ) from error
        trace_path = Path(raw_trace_path)
        trace_identity = (trace_stat.st_dev, trace_stat.st_ino)
        trace_name = (
            f"{self.name}/build-input-replay/file-access.strace"
        )

        build_environment = self.environment(
            replay_parent, context.run_context
        )
        build_environment["FIR_VALIDATION_BUILD_TOOLS"] = (
            self.tool_environment_value(self._built_build_tools)
        )
        executable_directories = sorted(
            {
                str(Path(str(binding["path"])).parent)
                for binding in bindings
                if binding["category"] == "build-input"
                and "exec" in binding["accesses"]
            }
        )
        replay_path = ":".join(
            dict.fromkeys((*executable_directories, "/usr/bin", "/bin"))
        )
        payload_environment = {
            "HOME": "/tmp/home",
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "PATH": replay_path,
            "TERM": "dumb",
            "TMPDIR": "/tmp",
        }
        payload_environment.update(build_environment)
        isolator_command = [
            str(isolator.source_path),
            "--die-with-parent",
            "--new-session",
            "--unshare-all",
            "--unshare-user",
            "--disable-userns",
            "--assert-userns-disabled",
            "--cap-drop",
            "ALL",
            "--hostname",
            "fir-validation",
            "--clearenv",
            "--ro-bind",
            "/",
            "/",
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--tmpfs",
            "/tmp",
            "--dir",
            "/tmp/home",
            "--bind",
            str(replay_backend),
            str(replay_backend),
        ]
        for key, value in sorted(payload_environment.items()):
            isolator_command.extend(("--setenv", key, value))
        overlay_fds: list[tuple[int, str, int]] = []
        try:
            for digest, content, target, mode, binding_context in overlay_specs:
                descriptor = sealed_snapshot_fd(
                    digest, content, mode, binding_context
                )
                overlay_fds.append((descriptor, target, mode))
                isolator_command.extend(
                    (
                        "--perms",
                        f"{mode:04o}",
                        "--ro-bind-data",
                        str(descriptor),
                        target,
                    )
                )
        except BaseException:
            for descriptor, _, _ in overlay_fds:
                close_file_descriptor(descriptor)
            raise
        status_read_fd = -1
        status_write_fd = -1
        try:
            status_read_fd, status_write_fd = os.pipe()
            inherited_status_fd = fcntl.fcntl(
                status_write_fd, fcntl.F_DUPFD_CLOEXEC, 4096
            )
            close_file_descriptor(status_write_fd)
            status_write_fd = inherited_status_fd
        except OSError as error:
            if status_read_fd >= 0:
                close_file_descriptor(status_read_fd)
            if status_write_fd >= 0:
                close_file_descriptor(status_write_fd)
            for descriptor, _, _ in overlay_fds:
                close_file_descriptor(descriptor)
            raise ValidationError(
                f"cannot create {self.name} replay status pipe: {error}"
            ) from error
        isolator_command.extend(
            ("--json-status-fd", str(status_write_fd))
        )
        isolator_command.extend(
            (
                "--chdir",
                str(context.root.resolve()),
                "--",
                *self._built_build_replay_command,
            )
        )
        command = [
            str(recorder.source_path),
            "-f",
            "-qq",
            "--kill-on-exit",
            "-s",
            "0",
            "-yy",
            "-X",
            "raw",
            "-e",
            "trace=open,openat,openat2,execve,execveat",
            "-e",
            "status=successful",
            "-e",
            "signal=none",
            "-o",
            str(trace_path),
            "--",
            *isolator_command,
        ]
        passed_descriptors = tuple(
            [descriptor for descriptor, _, _ in overlay_fds]
            + [status_write_fd]
        )
        try:
            try:
                completed = run(
                    command,
                    context.root,
                    self.timeout_seconds,
                    build_environment,
                    passed_descriptors,
                )
            finally:
                for descriptor in passed_descriptors:
                    close_file_descriptor(descriptor)
        except BaseException:
            close_file_descriptor(status_read_fd)
            raise
        try:
            status_chunks: list[bytes] = []
            while True:
                chunk = os.read(status_read_fd, 65536)
                if not chunk:
                    break
                status_chunks.append(chunk)
        except OSError as error:
            raise ValidationError(
                f"cannot read {self.name} replay status: {error}"
            ) from error
        finally:
            close_file_descriptor(status_read_fd)
        status_content = b"".join(status_chunks)
        destination = (
            context.out_dir / self.name / "build-input-replay"
        )
        process_artifacts = write_process_artifacts(
            destination,
            completed,
            f"{self.name}/build-input-replay",
        )
        self.verify_captured_tools(
            self._built_build_tools, "during build-input replay"
        )
        if completed.returncode != 0:
            raise ValidationError(
                f"failed to replay {self.name} build inputs; "
                f"see {destination}"
            )
        parse_bwrap_status(
            status_content, f"{self.name} build-input replay status"
        )
        status_name = (
            f"{self.name}/build-input-replay/sandbox-status.jsonl"
        )
        status_sha256 = sha256_bytes(status_content)
        status_artifact = ValidationArtifact(
            "build-input-replay-status",
            status_name,
            status_sha256,
            status_content,
        )
        if context.run_context is not None:
            self.verify_corpus(
                context.run_context, "during build-input replay"
            )
        if trace_path.is_symlink() or not trace_path.is_file():
            raise ValidationError(
                f"{self.name} build-input replay produced no trace"
            )
        try:
            final_trace_stat = trace_path.stat()
            trace_content = trace_path.read_bytes()
        except OSError as error:
            raise ValidationError(
                f"cannot read {self.name} build-input replay trace: {error}"
            ) from error
        if (
            final_trace_stat.st_dev,
            final_trace_stat.st_ino,
        ) != trace_identity:
            raise ValidationError(
                f"{self.name} build-input replay trace was replaced"
            )
        accesses = parse_build_file_access_trace(
            trace_content, f"{self.name} build-input replay trace"
        )
        trace_sha256 = sha256_bytes(trace_content)
        trace_artifact = ValidationArtifact(
            "build-input-replay-trace",
            trace_name,
            trace_sha256,
            trace_content,
        )
        for binding in bindings:
            expected_accesses = tuple(binding["accesses"])
            if binding["category"] == "validation-input":
                continue
            if accesses.get(str(binding["path"])) != expected_accesses:
                raise ValidationError(
                    f"{self.name} replay did not preserve accesses for "
                    f"{binding['category']}:{binding['kind']}:"
                    f"{binding['name']}"
                )
        replay_products = self.collect_products(replay_parent)
        if self.build_input_manifest is None:
            raise ValidationError(
                f"{self.name} build-input replay has no manifest"
            )
        _, replay_manifest_content = (
            validation_product_and_content_from_file(
                self.name,
                ProductDeclaration(
                    RESERVED_BUILD_INPUT_KIND,
                    self.build_input_manifest,
                ),
                replay_parent,
            )
        )
        replay_declarations = build_input_declarations_from_manifest(
            replay_manifest_content,
            f"{self.name} replay build input manifest",
        )
        source_members = {
            (item.kind, item.name): item
            for item in self._built_build_inputs
            if item.kind != RESERVED_BUILD_INPUT_KIND
        }
        replay_binding_paths = {
            (str(item["kind"]), str(item["name"])): str(item["path"])
            for item in bindings
            if item["category"] == "build-input"
        }
        declared_paths: dict[tuple[str, str], str] = {}
        for item in replay_declarations:
            key = (item.kind, item.name)
            raw_path = os.path.normpath(str(item.path))
            expected_path = replay_binding_paths.get(key)
            if (
                expected_path is not None
                and raw_path == f"{expected_path} (deleted)"
            ):
                raw_path = expected_path
            declared_paths[key] = raw_path
        if (
            set(declared_paths) != set(source_members)
            or declared_paths != replay_binding_paths
        ):
            raise ValidationError(
                f"{self.name} replay build input manifest does not match "
                "its immutable overlays"
            )
        replay_members = tuple(
            ValidationBuildInput(
                self.name,
                item.kind,
                item.name,
                source_members[(item.kind, item.name)].sha256,
                source_members[(item.kind, item.name)].content,
                Path(declared_paths[(item.kind, item.name)]),
            )
            for item in replay_declarations
        )
        canonical_replay_manifest = canonical_build_input_manifest_bytes(
            replay_members
        )
        replay_build_inputs = tuple(
            sorted(
                (
                    *replay_members,
                    ValidationBuildInput(
                        self.name,
                        RESERVED_BUILD_INPUT_KIND,
                        self.build_input_manifest,
                        sha256_bytes(canonical_replay_manifest),
                        canonical_replay_manifest,
                    ),
                ),
                key=lambda item: (item.kind, item.name),
            )
        )
        replay_manifest_name = (
            f"{self.name}/build-input-replay/build-input-manifest.json"
        )
        replay_manifest_sha256 = sha256_bytes(replay_manifest_content)
        replay_manifest_artifact = ValidationArtifact(
            "build-input-replay-manifest",
            replay_manifest_name,
            replay_manifest_sha256,
            replay_manifest_content,
        )
        access_record = self.bind_reported_inputs_to_file_accesses(
            "replay",
            {
                "trace": {
                    "name": trace_name,
                    "sha256": trace_sha256,
                },
                "accesses": [
                    {"path": path, "accesses": list(kinds)}
                    for path, kinds in accesses.items()
                ],
                "accessCount": len(accesses),
            },
            accesses,
            replay_build_inputs,
        )
        products_equal = replay_products == self._built_products
        build_inputs_equal = (
            replay_build_inputs == self._built_build_inputs
        )
        report = {
            "version": PROTOCOL_VERSION,
            "backend": self.name,
            "isolator": isolator.to_json(),
            "recorder": recorder.to_json(),
            "policy": {
                "mode": "content-addressed-declared-closure",
                "ambientRoot": "read-only",
                "network": "unshared",
                "nestedUserNamespaces": "disabled",
                "reportedInputs": "content-addressed-read-only-overlays",
                "temporaryDirectory": "fresh",
                "output": "isolated-writable",
            },
            "sourceAttempt": self.build_attempts,
            "command": list(self._built_build_replay_command),
            "cwd": str(context.root.resolve()),
            "environment": payload_environment,
            "writableRoot": str(replay_backend),
            "bindings": bindings,
            **access_record,
            "ambientAccessCount": len(
                set(accesses) - {str(binding["path"]) for binding in bindings}
            ),
            "sandboxStatus": {
                "name": status_name,
                "sha256": status_sha256,
            },
            "buildInputManifest": {
                "name": replay_manifest_name,
                "sha256": replay_manifest_sha256,
            },
            "products": [item.to_json() for item in replay_products],
            "buildInputs": [
                item.to_json() for item in replay_build_inputs
            ],
            "productsEqual": products_equal,
            "buildInputsEqual": build_inputs_equal,
            "equal": products_equal and build_inputs_equal,
        }
        report_content = (
            json.dumps(report, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8")
        report_path = context.out_dir / self.name / "build-input-replay.json"
        report_path.write_bytes(report_content)
        report_artifact = ValidationArtifact(
            "build-input-replay",
            f"{self.name}/build-input-replay.json",
            sha256_bytes(report_content),
            report_content,
        )
        findings: list[ValidationFinding] = []
        if not products_equal:
            findings.append(
                ValidationFinding(
                    "build-input-replay",
                    "content-addressed replay produced different products",
                    self.name,
                )
            )
        if not build_inputs_equal:
            findings.append(
                ValidationFinding(
                    "build-input-replay",
                    "content-addressed replay reported different build inputs",
                    self.name,
                )
            )
        return (
            (
                *process_artifacts,
                trace_artifact,
                status_artifact,
                replay_manifest_artifact,
                report_artifact,
            ),
            tuple(findings),
        )

    def build(self, context: BuildContext) -> None:
        self._built_products = None
        self._built_tools = None
        self._built_build_tools = None
        self._built_build_file_access_recorder = None
        self._built_execution_file_access_recorder = None
        self._built_build_input_replay_isolator = None
        self._built_build_inputs = None
        self._built_build_command = None
        self._built_build_replay_command = None
        self._built_run_command = None
        self._build_artifacts = ()
        self._build_findings = ()
        file_access_attempts: list[dict[str, object]] = []
        recorded_access: (
            tuple[dict[str, object], dict[str, tuple[str, ...]]] | None
        ) = None
        if not context.no_build and self.build_command:
            command_build_tools = self.collect_tools(
                context.root,
                self.build_tool_declarations
            )
            validation_build_tools: list[ValidationTool] = []
            if self.build_file_access_recorder is not None:
                if (
                    self.build_file_access_recorder.kind
                    != BUILD_FILE_ACCESS_RECORDER_KIND
                ):
                    raise ValidationError(
                        f"{self.name} build file-access recorder kind must be "
                        f"{BUILD_FILE_ACCESS_RECORDER_KIND}"
                    )
                self._built_build_file_access_recorder = (
                    validation_tool_from_declaration(
                        self.name,
                        self.build_file_access_recorder,
                        context.root,
                    )
                )
                validation_build_tools.append(
                    self._built_build_file_access_recorder
                )
            if self.build_input_replay_isolator is not None:
                if (
                    self.build_input_replay_isolator.kind
                    != BUILD_INPUT_REPLAY_ISOLATOR_KIND
                ):
                    raise ValidationError(
                        f"{self.name} build-input replay isolator kind "
                        f"must be {BUILD_INPUT_REPLAY_ISOLATOR_KIND}"
                    )
                self._built_build_input_replay_isolator = (
                    validation_tool_from_declaration(
                        self.name,
                        self.build_input_replay_isolator,
                        context.root,
                    )
                )
                validation_build_tools.append(
                    self._built_build_input_replay_isolator
                )
            self._built_build_tools = tuple(
                sorted(
                    (*command_build_tools, *validation_build_tools),
                    key=lambda tool: (tool.kind, tool.name),
                )
            )
            self._built_build_command = self.bind_command(
                context.root,
                self.build_command,
                self.build_tool_declarations,
                command_build_tools,
                "build",
            )
            if self.build_input_replay_isolator is not None:
                self._built_build_replay_command = self.bind_command(
                    context.root,
                    self.build_replay_command,
                    self.build_tool_declarations,
                    command_build_tools,
                    "build replay",
                )
            else:
                self._built_build_replay_command = tuple(
                    self.build_replay_command
                )
        else:
            self._built_build_tools = ()
            self._built_build_command = tuple(self.build_command)
            self._built_build_replay_command = tuple(
                self.build_replay_command
            )
        if not context.no_build and self.build_command:
            if self.product_manifest is not None:
                self.clear_dynamic_product_staging(context.out_dir)
            else:
                self.remove_stale_products(context.out_dir)
            destination = context.out_dir / self.name / "build"
            destination.mkdir(parents=True, exist_ok=True)
            build_environment = self.environment(
                context.out_dir, context.run_context
            )
            build_environment["FIR_VALIDATION_BUILD_TOOLS"] = (
                self.tool_environment_value(self._built_build_tools)
            )
            completed, attempt_artifacts, recorded_access = (
                self.run_build_attempt(
                    context,
                    1,
                    destination,
                    f"{self.name}/build",
                    build_environment,
                )
            )
            self._build_artifacts = attempt_artifacts
            self.verify_captured_tools(
                self._built_build_tools, "during build"
            )
            if completed.returncode != 0:
                raise ValidationError(
                    f"failed to build {self.name} validation backend; "
                    f"see {destination}"
                )
        if context.run_context is not None:
            self.verify_corpus(context.run_context, "during build")
        self._built_products = self.collect_products(context.out_dir)
        self._built_build_inputs = (
            self.collect_build_inputs(context.out_dir)
            if not context.no_build
            else ()
        )
        if recorded_access is not None:
            trace_record, accesses = recorded_access
            file_access_attempts.append(
                self.bind_reported_inputs_to_file_accesses(
                    1,
                    trace_record,
                    accesses,
                    self._built_build_inputs,
                )
            )
        if (
            not context.no_build
            and self.build_command
            and self.build_attempts > 1
        ):
            attempts = [
                {
                    "attempt": 1,
                    "products": [
                        product.to_json()
                        for product in self._built_products
                    ],
                    "buildInputs": [
                        item.to_json()
                        for item in self._built_build_inputs
                    ],
                }
            ]
            first_products = self._built_products
            first_build_inputs = tuple(
                ValidationBuildInput(
                    item.backend,
                    item.kind,
                    item.name,
                    item.sha256,
                )
                for item in self._built_build_inputs
            )
            findings: list[ValidationFinding] = []
            for attempt in range(2, self.build_attempts + 1):
                if self.product_manifest is not None:
                    self.clear_dynamic_product_staging(context.out_dir)
                else:
                    self.remove_stale_products(context.out_dir)
                destination = (
                    context.out_dir / self.name / f"build-{attempt}"
                )
                destination.mkdir(parents=True, exist_ok=True)
                build_environment = self.environment(
                    context.out_dir, context.run_context
                )
                build_environment["FIR_VALIDATION_BUILD_TOOLS"] = (
                    self.tool_environment_value(self._built_build_tools)
                )
                completed, attempt_artifacts, recorded_access = (
                    self.run_build_attempt(
                        context,
                        attempt,
                        destination,
                        f"{self.name}/build-{attempt}",
                        build_environment,
                    )
                )
                self._build_artifacts += attempt_artifacts
                self.verify_captured_tools(
                    self._built_build_tools,
                    f"during build attempt {attempt}",
                )
                if completed.returncode != 0:
                    raise ValidationError(
                        f"failed to build {self.name} validation backend "
                        f"on attempt {attempt}; see {destination}"
                    )
                if context.run_context is not None:
                    self.verify_corpus(
                        context.run_context,
                        f"during build attempt {attempt}",
                    )
                products = self.collect_products(context.out_dir)
                build_inputs = self.collect_build_inputs(context.out_dir)
                if recorded_access is not None:
                    trace_record, accesses = recorded_access
                    file_access_attempts.append(
                        self.bind_reported_inputs_to_file_accesses(
                            attempt,
                            trace_record,
                            accesses,
                            build_inputs,
                        )
                    )
                attempts.append(
                    {
                        "attempt": attempt,
                        "products": [
                            product.to_json() for product in products
                        ],
                        "buildInputs": [
                            item.to_json() for item in build_inputs
                        ],
                    }
                )
                if products != first_products:
                    findings.append(
                        ValidationFinding(
                            "build-determinism",
                            f"build attempt {attempt} produced different products",
                            self.name,
                        )
                    )
                if build_inputs != first_build_inputs:
                    findings.append(
                        ValidationFinding(
                            "build-determinism",
                            f"build attempt {attempt} reported different build inputs",
                            self.name,
                        )
                    )
                self._built_products = products
                self._built_build_inputs = build_inputs
            report = {
                "version": PROTOCOL_VERSION,
                "backend": self.name,
                "equal": not findings,
                "attempts": attempts,
            }
            report_content = (
                json.dumps(report, indent=2, sort_keys=True) + "\n"
            ).encode("utf-8")
            report_path = (
                context.out_dir / self.name / "build-determinism.json"
            )
            report_path.write_bytes(report_content)
            self._build_artifacts += (
                ValidationArtifact(
                    "build-determinism",
                    f"{self.name}/build-determinism.json",
                    sha256_bytes(report_content),
                    report_content,
                ),
            )
            self._build_findings = tuple(findings)
        if file_access_attempts:
            recorder = self._built_build_file_access_recorder
            if recorder is None:
                raise ValidationError(
                    f"{self.name} build file-access report has no recorder"
                )
            report = {
                "version": PROTOCOL_VERSION,
                "backend": self.name,
                "recorder": recorder.to_json(),
                "accessSetsEqual": all(
                    attempt["accesses"]
                    == file_access_attempts[0]["accesses"]
                    for attempt in file_access_attempts[1:]
                ),
                "reportedInputsEqual": all(
                    attempt["reportedInputs"]
                    == file_access_attempts[0]["reportedInputs"]
                    for attempt in file_access_attempts[1:]
                ),
                "attempts": file_access_attempts,
            }
            report_content = (
                json.dumps(report, indent=2, sort_keys=True) + "\n"
            ).encode("utf-8")
            report_path = (
                context.out_dir / self.name / "build-file-access.json"
            )
            report_path.write_bytes(report_content)
            self._build_artifacts += (
                ValidationArtifact(
                    "build-file-access",
                    f"{self.name}/build-file-access.json",
                    sha256_bytes(report_content),
                    report_content,
                ),
            )
        if (
            not context.no_build
            and self.build_input_replay_isolator is not None
        ):
            if recorded_access is None:
                raise ValidationError(
                    f"{self.name} build-input replay has no source trace"
                )
            _, source_accesses = recorded_access
            replay_artifacts, replay_findings = (
                self.run_build_input_replay(context, source_accesses)
            )
            self._build_artifacts += replay_artifacts
            self._build_findings += replay_findings
        self._built_tools = self.collect_tools(
            context.root, self.tool_declarations
        )
        if self.execution_file_access_recorder is not None:
            self._built_execution_file_access_recorder = (
                validation_tool_from_declaration(
                    self.name,
                    self.execution_file_access_recorder,
                    context.root,
                )
            )
        self._built_run_command = self.bind_command(
            context.root,
            self.run_command,
            self.tool_declarations,
            self._built_tools,
            "run",
        )

    def run_execution(
        self,
        context: RunContext,
        environment: dict[str, str],
    ) -> tuple[
        subprocess.CompletedProcess[str],
        tuple[ValidationArtifact, ...],
        tuple[dict[str, str], dict[str, tuple[str, ...]]] | None,
    ]:
        command = list(self._built_run_command or ())
        recorder = self._built_execution_file_access_recorder
        if recorder is None:
            return (
                run(
                    command,
                    context.root,
                    self.timeout_seconds,
                    environment,
                ),
                (),
                None,
            )
        if recorder.source_path is None:
            raise ValidationError(
                f"{self.name} execution file-access recorder has no source path"
            )
        trace_root = (
            context.out_dir.resolve() / "execution-file-access-traces"
        )
        if trace_root.is_symlink() or (
            trace_root.exists() and not trace_root.is_dir()
        ):
            raise ValidationError(
                f"{self.name} execution file-access trace root is not a directory"
            )
        trace_root.mkdir(parents=True, exist_ok=True)
        trace_fd = -1
        try:
            trace_fd, raw_trace_path = tempfile.mkstemp(
                prefix=f"{self.name}-execute-",
                suffix=".strace",
                dir=trace_root,
            )
            trace_stat = os.fstat(trace_fd)
        except OSError as error:
            raise ValidationError(
                f"cannot create {self.name} execution file-access trace: "
                f"{error}"
            ) from error
        finally:
            if trace_fd >= 0:
                close_file_descriptor(trace_fd)
        trace_path = Path(raw_trace_path)
        trace_identity = (trace_stat.st_dev, trace_stat.st_ino)
        trace_name = f"{self.name}/execute/file-access.strace"
        completed = run(
            [
                str(recorder.source_path),
                "-f",
                "-qq",
                "--kill-on-exit",
                "-s",
                "0",
                "-yy",
                "-X",
                "raw",
                "-e",
                "trace=open,openat,openat2,execve,execveat",
                "-e",
                "status=successful",
                "-e",
                "signal=none",
                "-o",
                str(trace_path),
                "--",
                *command,
            ],
            context.root,
            self.timeout_seconds,
            environment,
        )
        if trace_path.is_symlink() or not trace_path.is_file():
            raise ValidationError(
                f"{self.name} execution file-access recorder produced no trace"
            )
        try:
            final_trace_stat = trace_path.stat()
            trace_content = trace_path.read_bytes()
        except OSError as error:
            raise ValidationError(
                f"cannot read {self.name} execution file-access trace: {error}"
            ) from error
        if (
            final_trace_stat.st_dev,
            final_trace_stat.st_ino,
        ) != trace_identity:
            raise ValidationError(
                f"{self.name} execution file-access trace was replaced"
            )
        trace_sha256 = sha256_bytes(trace_content)
        accesses = parse_file_access_trace(
            trace_content, f"{self.name} execution file-access trace"
        )
        trace_artifact = ValidationArtifact(
            "execution-file-access-trace",
            trace_name,
            trace_sha256,
            trace_content,
        )
        return completed, (trace_artifact,), (
            {"name": trace_name, "sha256": trace_sha256},
            accesses,
        )

    def execution_file_access_artifact(
        self,
        context: RunContext,
        bundle: ProductBundle | None,
        results: dict[str, dict],
        recorded_access: (
            tuple[dict[str, str], dict[str, tuple[str, ...]]] | None
        ),
    ) -> tuple[ValidationArtifact, ...]:
        recorder = self._built_execution_file_access_recorder
        if recorder is None:
            if recorded_access is not None:
                raise ValidationError(
                    f"{self.name} has undeclared execution file-access evidence"
                )
            return ()
        if bundle is None or recorded_access is None:
            raise ValidationError(
                f"{self.name} execution file-access recorder has no provider bundle"
            )
        trace, accesses = recorded_access
        receipts = [
            checked_product_bundle_receipt(
                record, self.name, case_id, bundle
            )
            for case_id, record in sorted(results.items())
        ]
        receipted_products = {
            (product.backend, product.kind, product.name, product.sha256): product
            for receipt in receipts
            for product in receipt.products
        }
        product_accesses: list[dict[str, object]] = []
        for product in sorted(
            receipted_products.values(),
            key=lambda item: (item.backend, item.kind, item.name),
        ):
            path = os.path.normpath(
                str(
                    (
                        context.out_dir
                        / product.backend
                        / product.name
                    ).resolve()
                )
            )
            observed = accesses.get(path)
            if observed is None or "read" not in observed:
                raise ValidationError(
                    f"{self.name} execution did not open receipted product "
                    f"{product.kind}:{product.name}"
                )
            product_accesses.append(
                {
                    **product.to_json(),
                    "path": path,
                    "accesses": list(observed),
                }
            )
        report = {
            "version": PROTOCOL_VERSION,
            "backend": self.name,
            "recorder": recorder.to_json(),
            "provider": bundle.provider,
            "bundleSha256": bundle.bundle_sha256,
            "trace": trace,
            "receiptCount": len(receipts),
            "products": product_accesses,
            "productCount": len(product_accesses),
            "accessCount": len(accesses),
        }
        report_content = (
            json.dumps(report, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8")
        report_path = context.out_dir / self.name / "execution-file-access.json"
        report_path.write_bytes(report_content)
        return (
            ValidationArtifact(
                "execution-file-access",
                f"{self.name}/execution-file-access.json",
                sha256_bytes(report_content),
                report_content,
            ),
        )

    def execute(self, context: RunContext) -> BackendRun:
        destination = context.out_dir / self.name
        destination.mkdir(parents=True, exist_ok=True)
        if (
            self._built_products is None
            or self._built_tools is None
            or self._built_build_tools is None
            or self._built_build_inputs is None
            or self._built_run_command is None
        ):
            raise ValidationError(
                f"{self.name} adapter must be built before execution"
            )
        self.verify_corpus(context, "before execution")
        if self.collect_products(context.out_dir) != self._built_products:
            raise ValidationError(
                f"{self.name} products changed between build and execution"
            )
        if (
            self.build_input_manifest is not None
            and self._built_build_inputs
            and self.collect_build_inputs(context.out_dir)
            != self._built_build_inputs
        ):
            raise ValidationError(
                f"{self.name} build inputs changed between build and execution"
            )
        execution_recorder_tools = (
            (self._built_execution_file_access_recorder,)
            if self._built_execution_file_access_recorder is not None
            else ()
        )
        self.verify_captured_tools(
            (
                *self._built_build_tools,
                *self._built_tools,
                *execution_recorder_tools,
            ),
            "between build and execution",
        )
        bundle = None
        exposed_products = self._built_products
        if self.product_provider is not None:
            bundle = context.product_bundles.get(self.product_provider.provider)
            if bundle is None:
                raise ValidationError(
                    f"{self.name} requires missing product provider "
                    f"{self.product_provider.provider}"
                )
            if bundle.contract != self.product_provider.contract:
                raise ValidationError(
                    f"{self.name} product contract disagrees with provider "
                    f"{bundle.provider}"
                )
            exposed_products = bundle.products
            verify_product_bundle_files(
                context, bundle, f"before {self.name} execution"
            )
        execution_input_value_ = execution_input_value(
            self.name,
            context.selected,
            exposed_products,
            bundle,
            context.out_dir,
        )
        checked_execution_input(
            canonical_json_bytes(execution_input_value_),
            self.name,
            context.selected,
            exposed_products,
            bundle,
            f"{self.name} execution input",
            context.out_dir,
        )
        execution_input = materialize_execution_input(
            context.out_dir,
            self.name,
            execution_input_value_,
        )
        environment = self.environment(context.out_dir, context)
        environment.pop("FIR_VALIDATION_CASES", None)
        environment.update(
            {
                "FIR_VALIDATION_EXECUTION_INPUT": str(
                    execution_input.path.resolve()
                ),
                "FIR_VALIDATION_TOOLS": self.tool_environment_value(
                    self._built_tools
                ),
                "FIR_VALIDATION_BUILD_TOOLS": self.tool_environment_value(
                    self._built_build_tools
                ),
            }
        )
        completed, access_artifacts, recorded_access = self.run_execution(
            context, environment
        )
        execution_input.verify("during execution")
        if bundle is not None:
            verify_product_bundle_files(
                context, bundle, f"during {self.name} execution"
            )
        execution_artifacts = write_process_artifacts(
            destination, completed, self.name
        )
        if self.collect_products(context.out_dir) != self._built_products:
            raise ValidationError(
                f"{self.name} products changed during execution"
            )
        if (
            self.build_input_manifest is not None
            and self._built_build_inputs
            and self.collect_build_inputs(context.out_dir)
            != self._built_build_inputs
        ):
            raise ValidationError(
                f"{self.name} build inputs changed during execution"
            )
        self.verify_corpus(context, "during execution")
        self.verify_captured_tools(
            (
                *self._built_build_tools,
                *self._built_tools,
                *execution_recorder_tools,
            ),
            "during execution",
        )
        expected_cases = (
            context.selected
            if self.result_domain == "selected"
            else context.all_cases
        )
        backend_run = BackendRun(
            self.name,
            list(expected_cases),
            findings=list(self._build_findings),
            products=list(self._built_products),
            tools=[
                *self._built_build_tools,
                *self._built_tools,
                *execution_recorder_tools,
            ],
            build_inputs=list(self._built_build_inputs),
            artifacts=[
                *self._build_artifacts,
                execution_input.artifact,
                *execution_artifacts,
                *access_artifacts,
            ],
        )
        if completed.returncode != 0:
            backend_run.artifacts.extend(
                self.execution_file_access_artifact(
                    context, bundle, {}, recorded_access
                )
            )
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
            records_from_output(
                completed.stdout, list(self._built_run_command)
            ),
            self.name,
        )
        backend_run.artifacts.extend(
            self.execution_file_access_artifact(
                context, bundle, backend_run.results, recorded_access
            )
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
    optional = {
        "buildCommand",
        "buildReplayCommand",
        "buildAttempts",
        "timeoutSeconds",
        "products",
        "productManifest",
        "buildInputManifest",
        "buildFileAccessRecorder",
        "executionFileAccessRecorder",
        "buildInputReplay",
        "tools",
        "buildTools",
        "productProvider",
    }
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
    build_replay_command = checked_command("buildReplayCommand", False)
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
    build_attempts = value.get("buildAttempts", 1)
    if (
        not isinstance(build_attempts, int)
        or isinstance(build_attempts, bool)
        or build_attempts <= 0
    ):
        raise ValidationError(
            f"adapter config {path}: buildAttempts must be a positive integer"
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
        if kind == RESERVED_PRODUCT_KIND:
            raise ValidationError(
                f"{product_context}: product kind is reserved"
            )
        product_path = checked_relative_posix_path(
            product["path"], product_context
        )
        if product_path in RESERVED_PRODUCT_PATHS:
            raise ValidationError(
                f"{product_context}: product path is reserved by the harness"
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
    raw_product_manifest = value.get("productManifest")
    product_manifest = None
    if raw_product_manifest is not None:
        product_manifest = checked_relative_posix_path(
            raw_product_manifest,
            f"adapter config {path}: productManifest",
        )
        if product_manifest in RESERVED_PRODUCT_PATHS:
            raise ValidationError(
                f"adapter config {path}: productManifest path is reserved "
                "by the harness"
            )
        if product_declarations:
            raise ValidationError(
                f"adapter config {path}: products and productManifest are "
                "mutually exclusive"
            )
        if not build_command:
            raise ValidationError(
                f"adapter config {path}: productManifest requires buildCommand"
            )
    raw_product_provider = value.get("productProvider")
    product_provider = None
    if raw_product_provider is not None:
        if not isinstance(raw_product_provider, dict) or set(
            raw_product_provider
        ) != {"name", "contract"}:
            raise ValidationError(
                f"adapter config {path}: productProvider must contain name "
                "and contract"
            )
        product_provider = ProductProviderRequirement(
            validate_backend_name(
                raw_product_provider["name"],
                f"adapter config {path}: product provider",
            ),
            product_contract_from_json(
                raw_product_provider["contract"],
                f"adapter config {path}: product provider contract",
            ),
        )
        if build_command or product_declarations or product_manifest is not None:
            raise ValidationError(
                f"adapter config {path}: productProvider cannot be combined "
                "with adapter-owned builds or products"
            )
        if result_domain != "selected":
            raise ValidationError(
                f"adapter config {path}: productProvider requires "
                "resultDomain 'selected'"
            )
    if build_attempts > 1 and not build_command:
        raise ValidationError(
            f"adapter config {path}: multiple buildAttempts require buildCommand"
        )
    if (
        build_attempts > 1
        and not product_declarations
        and product_manifest is None
    ):
        raise ValidationError(
            f"adapter config {path}: multiple buildAttempts require products"
        )
    raw_build_input_manifest = value.get("buildInputManifest")
    build_input_manifest = None
    if raw_build_input_manifest is not None:
        build_input_manifest = checked_relative_posix_path(
            raw_build_input_manifest,
            f"adapter config {path}: buildInputManifest",
        )
        if build_input_manifest in RESERVED_PRODUCT_PATHS:
            raise ValidationError(
                f"adapter config {path}: buildInputManifest path is "
                "reserved by the harness"
            )
        if (
            build_input_manifest == product_manifest
            or build_input_manifest in product_paths
        ):
            raise ValidationError(
                f"adapter config {path}: buildInputManifest path collides "
                "with a product path"
            )
        if not build_command:
            raise ValidationError(
                f"adapter config {path}: buildInputManifest requires "
                "buildCommand"
            )
    def checked_tools(
        field_name: str, owning_command: list[str], command_field: str
    ) -> tuple[ToolDeclaration, ...]:
        tool_label = "tool" if field_name == "tools" else "build tool"
        raw_tools = value.get(field_name, [])
        if not isinstance(raw_tools, list):
            raise ValidationError(
                f"adapter config {path}: {field_name} must be an object array"
            )
        tool_declarations: list[ToolDeclaration] = []
        tool_keys: set[tuple[str, str]] = set()
        tool_sources: set[tuple[str, str]] = set()
        for index, tool in enumerate(raw_tools):
            tool_context = f"adapter config {path}/{field_name}/{index}"
            if not isinstance(tool, dict):
                raise ValidationError(f"{tool_context}: expected an object")
            fields = set(tool)
            locator_fields = fields & {"path", "command"}
            if (
                not {"kind", "name"} <= fields
                or not fields
                <= {
                    "kind",
                    "name",
                    "path",
                    "command",
                    "resolveCommand",
                }
                or len(locator_fields) != 1
                or ("resolveCommand" in fields and "command" not in fields)
            ):
                raise ValidationError(
                    f"{tool_context}: expected kind, name, and exactly one of "
                    "path or command; resolveCommand requires command"
                )
            kind = validate_backend_name(tool["kind"], tool_context)
            if kind in {
                BUILD_FILE_ACCESS_RECORDER_KIND,
                EXECUTION_FILE_ACCESS_RECORDER_KIND,
                BUILD_INPUT_REPLAY_ISOLATOR_KIND,
            }:
                owning_field = {
                    BUILD_FILE_ACCESS_RECORDER_KIND: "buildFileAccessRecorder",
                    EXECUTION_FILE_ACCESS_RECORDER_KIND:
                        "executionFileAccessRecorder",
                    BUILD_INPUT_REPLAY_ISOLATOR_KIND: "buildInputReplay",
                }[kind]
                raise ValidationError(
                    f"{tool_context}: tool kind is reserved for "
                    f"{owning_field}"
                )
            tool_name = checked_relative_posix_path(
                tool["name"], tool_context
            )
            key = (kind, tool_name)
            if key in tool_keys:
                raise ValidationError(
                    f"adapter config {path}: duplicate {tool_label}: "
                    f"{kind}:{tool_name}"
                )
            tool_keys.add(key)
            if "path" in tool:
                raw_path = checked_config_relative_posix_path(
                    tool["path"], tool_context
                )
                declaration = ToolDeclaration(
                    kind,
                    tool_name,
                    path=Path(os.path.abspath(path.parent / raw_path)),
                )
            else:
                command = tool["command"]
                if (
                    not isinstance(command, str)
                    or not command
                    or "\x00" in command
                    or "/" in command
                    or "\\" in command
                ):
                    raise ValidationError(
                        f"{tool_context}: command must be a bare PATH command"
                    )
                raw_resolve_command = tool.get("resolveCommand")
                resolve_command = None
                if raw_resolve_command is not None:
                    if (
                        not isinstance(raw_resolve_command, list)
                        or not raw_resolve_command
                        or not all(
                            isinstance(argument, str)
                            and argument
                            and "\x00" not in argument
                            for argument in raw_resolve_command
                        )
                    ):
                        raise ValidationError(
                            f"{tool_context}: resolveCommand must be a "
                            "nonempty argv array"
                        )
                    resolve_command = tuple(raw_resolve_command)
                declaration = ToolDeclaration(
                    kind,
                    tool_name,
                    command=command,
                    resolve_command=resolve_command,
                )
            source = (
                ("path", str(declaration.path))
                if declaration.path is not None
                else ("command", str(declaration.command))
            )
            if source in tool_sources:
                raise ValidationError(
                    f"adapter config {path}: duplicate {tool_label} "
                    f"source: {source[1]}"
                )
            tool_sources.add(source)
            tool_declarations.append(declaration)
        if not owning_command:
            if tool_declarations:
                raise ValidationError(
                    f"adapter config {path}: {field_name} requires "
                    f"{command_field}"
                )
            return ()
        if not tool_declarations:
            raise ValidationError(
                f"adapter config {path}: {field_name} must be nonempty"
            )
        command_declarations = [
            declaration
            for declaration in tool_declarations
            if declaration.command is not None
        ]
        if len(command_declarations) != 1:
            raise ValidationError(
                f"adapter config {path}: {field_name} must contain exactly "
                "one command"
            )
        if command_declarations[0].command != owning_command[0]:
            raise ValidationError(
                f"adapter config {path}: {field_name} command tool must "
                f"match {command_field}[0]"
            )
        return tuple(
            sorted(
                tool_declarations,
                key=lambda declaration: (declaration.kind, declaration.name),
            )
        )

    tool_declarations = checked_tools("tools", run_command, "runCommand")
    build_tool_declarations = checked_tools(
        "buildTools", build_command, "buildCommand"
    )
    raw_build_file_access_recorder = value.get(
        "buildFileAccessRecorder"
    )
    build_file_access_recorder = None
    if raw_build_file_access_recorder is not None:
        recorder_context = (
            f"adapter config {path}/buildFileAccessRecorder"
        )
        if (
            not isinstance(raw_build_file_access_recorder, dict)
            or set(raw_build_file_access_recorder)
            != {"kind", "name", "command"}
        ):
            raise ValidationError(
                f"{recorder_context}: expected kind, name, and command fields"
            )
        recorder_kind = validate_backend_name(
            raw_build_file_access_recorder["kind"], recorder_context
        )
        if recorder_kind != BUILD_FILE_ACCESS_RECORDER_KIND:
            raise ValidationError(
                f"{recorder_context}: kind must be "
                f"{BUILD_FILE_ACCESS_RECORDER_KIND}"
            )
        recorder_name = checked_relative_posix_path(
            raw_build_file_access_recorder["name"], recorder_context
        )
        recorder_command = raw_build_file_access_recorder["command"]
        if (
            not isinstance(recorder_command, str)
            or not recorder_command
            or "\x00" in recorder_command
            or "/" in recorder_command
            or "\\" in recorder_command
        ):
            raise ValidationError(
                f"{recorder_context}: command must be a bare PATH command"
            )
        if not build_command:
            raise ValidationError(
                f"adapter config {path}: buildFileAccessRecorder requires "
                "buildCommand"
            )
        build_file_access_recorder = ToolDeclaration(
            recorder_kind,
            recorder_name,
            command=recorder_command,
        )
    raw_execution_file_access_recorder = value.get(
        "executionFileAccessRecorder"
    )
    execution_file_access_recorder = None
    if raw_execution_file_access_recorder is not None:
        recorder_context = (
            f"adapter config {path}/executionFileAccessRecorder"
        )
        if (
            not isinstance(raw_execution_file_access_recorder, dict)
            or set(raw_execution_file_access_recorder)
            != {"kind", "name", "command"}
        ):
            raise ValidationError(
                f"{recorder_context}: expected kind, name, and command fields"
            )
        recorder_kind = validate_backend_name(
            raw_execution_file_access_recorder["kind"], recorder_context
        )
        if recorder_kind != EXECUTION_FILE_ACCESS_RECORDER_KIND:
            raise ValidationError(
                f"{recorder_context}: kind must be "
                f"{EXECUTION_FILE_ACCESS_RECORDER_KIND}"
            )
        recorder_name = checked_relative_posix_path(
            raw_execution_file_access_recorder["name"], recorder_context
        )
        recorder_command = raw_execution_file_access_recorder["command"]
        if (
            not isinstance(recorder_command, str)
            or not recorder_command
            or "\x00" in recorder_command
            or "/" in recorder_command
            or "\\" in recorder_command
        ):
            raise ValidationError(
                f"{recorder_context}: command must be a bare PATH command"
            )
        if recorder_name != recorder_command:
            raise ValidationError(
                f"{recorder_context}: name must equal command to bind the "
                "retained tool identity"
            )
        if product_provider is None:
            raise ValidationError(
                f"adapter config {path}: executionFileAccessRecorder "
                "requires productProvider"
            )
        execution_file_access_recorder = ToolDeclaration(
            recorder_kind,
            recorder_name,
            command=recorder_command,
        )
    raw_build_input_replay = value.get("buildInputReplay")
    build_input_replay_isolator = None
    if raw_build_input_replay is not None:
        replay_context = f"adapter config {path}/buildInputReplay"
        if (
            not isinstance(raw_build_input_replay, dict)
            or set(raw_build_input_replay)
            != {"kind", "name", "command"}
        ):
            raise ValidationError(
                f"{replay_context}: expected kind, name, and command fields"
            )
        replay_kind = validate_backend_name(
            raw_build_input_replay["kind"], replay_context
        )
        if replay_kind != BUILD_INPUT_REPLAY_ISOLATOR_KIND:
            raise ValidationError(
                f"{replay_context}: kind must be "
                f"{BUILD_INPUT_REPLAY_ISOLATOR_KIND}"
            )
        replay_name = checked_relative_posix_path(
            raw_build_input_replay["name"], replay_context
        )
        replay_command = raw_build_input_replay["command"]
        if (
            not isinstance(replay_command, str)
            or not replay_command
            or "\x00" in replay_command
            or "/" in replay_command
            or "\\" in replay_command
        ):
            raise ValidationError(
                f"{replay_context}: command must be a bare PATH command"
            )
        if not build_command:
            raise ValidationError(
                f"adapter config {path}: buildInputReplay requires "
                "buildCommand"
            )
        if not build_replay_command:
            raise ValidationError(
                f"adapter config {path}: buildInputReplay requires "
                "buildReplayCommand"
            )
        if build_input_manifest is None:
            raise ValidationError(
                f"adapter config {path}: buildInputReplay requires "
                "buildInputManifest"
            )
        if build_file_access_recorder is None:
            raise ValidationError(
                f"adapter config {path}: buildInputReplay requires "
                "buildFileAccessRecorder"
            )
        build_input_replay_isolator = ToolDeclaration(
            replay_kind,
            replay_name,
            command=replay_command,
        )
    if build_replay_command and build_input_replay_isolator is None:
        raise ValidationError(
            f"adapter config {path}: buildReplayCommand requires "
            "buildInputReplay"
        )
    if build_replay_command:
        replay_command_tools = [
            declaration
            for declaration in build_tool_declarations
            if declaration.command is not None
        ]
        if (
            len(replay_command_tools) != 1
            or replay_command_tools[0].command != build_replay_command[0]
        ):
            raise ValidationError(
                f"adapter config {path}: buildTools command tool must "
                "match buildReplayCommand[0]"
            )
    duplicate_tool_keys = sorted(
        {
            (declaration.kind, declaration.name)
            for declaration in tool_declarations
        }
        & {
            (declaration.kind, declaration.name)
            for declaration in build_tool_declarations
        }
    )
    if duplicate_tool_keys:
        kind, tool_name = duplicate_tool_keys[0]
        raise ValidationError(
            f"adapter config {path}: duplicate tool across build and run: "
            f"{kind}:{tool_name}"
        )
    if build_file_access_recorder is not None:
        existing_declarations = (
            *tool_declarations,
            *build_tool_declarations,
        )
        recorder_key = (
            build_file_access_recorder.kind,
            build_file_access_recorder.name,
        )
        if recorder_key in {
            (declaration.kind, declaration.name)
            for declaration in existing_declarations
        }:
            raise ValidationError(
                f"adapter config {path}: duplicate file-access recorder "
                f"tool: {recorder_key[0]}:{recorder_key[1]}"
            )
        if (
            "command",
            str(build_file_access_recorder.command),
        ) in {
            (
                ("path", str(declaration.path))
                if declaration.path is not None
                else ("command", str(declaration.command))
            )
            for declaration in existing_declarations
        }:
            raise ValidationError(
                f"adapter config {path}: duplicate file-access recorder "
                f"source: {build_file_access_recorder.command}"
            )
    if build_input_replay_isolator is not None:
        existing_declarations = (
            *tool_declarations,
            *build_tool_declarations,
            build_file_access_recorder,
        )
        replay_key = (
            build_input_replay_isolator.kind,
            build_input_replay_isolator.name,
        )
        if replay_key in {
            (declaration.kind, declaration.name)
            for declaration in existing_declarations
        }:
            raise ValidationError(
                f"adapter config {path}: duplicate build-input replay "
                f"tool: {replay_key[0]}:{replay_key[1]}"
            )
        if (
            "command",
            str(build_input_replay_isolator.command),
        ) in {
            (
                ("path", str(declaration.path))
                if declaration.path is not None
                else ("command", str(declaration.command))
            )
            for declaration in existing_declarations
        }:
            raise ValidationError(
                f"adapter config {path}: duplicate build-input replay "
                f"source: {build_input_replay_isolator.command}"
            )
    if execution_file_access_recorder is not None:
        existing_declarations = tuple(
            declaration
            for declaration in (
                *tool_declarations,
                *build_tool_declarations,
                build_file_access_recorder,
                build_input_replay_isolator,
            )
            if declaration is not None
        )
        recorder_key = (
            execution_file_access_recorder.kind,
            execution_file_access_recorder.name,
        )
        if recorder_key in {
            (declaration.kind, declaration.name)
            for declaration in existing_declarations
        }:
            raise ValidationError(
                f"adapter config {path}: duplicate execution file-access "
                f"recorder tool: {recorder_key[0]}:{recorder_key[1]}"
            )
        if (
            "command",
            str(execution_file_access_recorder.command),
        ) in {
            (
                ("path", str(declaration.path))
                if declaration.path is not None
                else ("command", str(declaration.command))
            )
            for declaration in existing_declarations
        }:
            raise ValidationError(
                f"adapter config {path}: duplicate execution file-access "
                f"recorder source: {execution_file_access_recorder.command}"
            )
    return ExternalCommandAdapter(
        name=name,
        run_command=run_command,
        result_domain=result_domain,
        build_command=build_command,
        build_replay_command=build_replay_command,
        timeout_seconds=timeout_seconds,
        product_declarations=tuple(
            sorted(
                product_declarations,
                key=lambda declaration: (declaration.kind, declaration.path),
            )
        ),
        product_manifest=product_manifest,
        build_input_manifest=build_input_manifest,
        build_file_access_recorder=build_file_access_recorder,
        execution_file_access_recorder=execution_file_access_recorder,
        build_input_replay_isolator=build_input_replay_isolator,
        build_attempts=build_attempts,
        tool_declarations=tool_declarations,
        build_tool_declarations=build_tool_declarations,
        product_provider=product_provider,
    )


@dataclass
class ExternalProductProvider:
    """Product provider reusing the external adapter's hermetic build path."""

    name: str
    contract: ProductContract
    bundle_manifest: str
    driver: ExternalCommandAdapter

    def build(self, context: BuildContext) -> ProductProviderRun:
        if context.run_context is None:
            raise ValidationError(
                f"{self.name} provider requires a validation run context"
            )
        self.driver.build(context)
        products = self.driver._built_products
        tools = self.driver._built_tools
        build_tools = self.driver._built_build_tools
        build_inputs = self.driver._built_build_inputs
        if (
            products is None
            or tools is None
            or build_tools is None
            or build_inputs is None
        ):
            raise ValidationError(f"{self.name} provider build is incomplete")
        _, content = validation_product_and_content_from_file(
            self.name,
            ProductDeclaration(RESERVED_PRODUCT_KIND, self.bundle_manifest),
            context.out_dir,
        )
        bundle = product_bundle_from_manifest(
            self.name,
            self.contract,
            content,
            products,
            context.run_context.selected,
            f"{self.name} product bundle manifest",
        )
        return ProductProviderRun(
            self.name,
            bundle,
            products=list(products),
            findings=list(self.driver._build_findings),
            tools=[*build_tools, *tools],
            build_inputs=list(build_inputs),
            artifacts=list(self.driver._build_artifacts),
        )


def external_product_provider_from_config(
    path: Path, content: bytes | None = None
) -> ExternalProductProvider:
    """Load a strict build-only provider config."""
    try:
        source = path.read_bytes() if content is None else content
        value = json.loads(source.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"cannot read product provider config {path}: {error}"
        ) from error
    if not isinstance(value, dict):
        raise ValidationError(
            f"product provider config {path}: expected a JSON object"
        )
    required = {
        "version", "name", "contract", "buildCommand", "bundleManifest"
    }
    optional = {
        "buildReplayCommand",
        "buildAttempts",
        "timeoutSeconds",
        "buildInputManifest",
        "buildFileAccessRecorder",
        "buildInputReplay",
        "buildTools",
    }
    missing = sorted(required - value.keys())
    unknown = sorted(value.keys() - required - optional)
    if missing:
        raise ValidationError(
            f"product provider config {path}: missing fields: "
            + ", ".join(missing)
        )
    if unknown:
        raise ValidationError(
            f"product provider config {path}: unknown fields: "
            + ", ".join(unknown)
        )
    if (
        not isinstance(value["version"], int)
        or isinstance(value["version"], bool)
        or value["version"] != PROTOCOL_VERSION
    ):
        raise ValidationError(
            f"product provider config {path}: unsupported version"
        )
    name = validate_backend_name(
        value["name"], f"product provider config {path}"
    )
    contract = product_contract_from_json(
        value["contract"], f"product provider config {path}/contract"
    )
    bundle_manifest = checked_relative_posix_path(
        value["bundleManifest"],
        f"product provider config {path}: bundleManifest",
    )
    adapter_value = {
        key: item for key, item in value.items()
        if key not in {"version", "contract", "bundleManifest"}
    }
    adapter_value.update(
        {
            # The shared build parser requires an execution tool. It is
            # discarded immediately below; providers never execute it.
            "runCommand": ["true"],
            "resultDomain": "selected",
            "productManifest": bundle_manifest,
            "tools": [
                {
                    "kind": "provider-placeholder",
                    "name": "true",
                    "command": "true",
                }
            ],
        }
    )
    driver = external_adapter_from_config(
        path,
        (json.dumps(adapter_value, sort_keys=True) + "\n").encode("utf-8"),
    )
    driver.run_command = []
    driver.tool_declarations = ()
    return ExternalProductProvider(
        name, contract, bundle_manifest, driver
    )


@dataclass(frozen=True)
class ValidationPlan:
    adapter_configs: tuple[Path, ...]
    pairs: tuple[tuple[str, str], ...]
    provider_configs: tuple[Path, ...] = ()
    corpus_backend: str = "native"
    exclude_tags: tuple[str, ...] = ()


@dataclass(frozen=True)
class ValidationPlanDeclaration:
    adapter_configs: tuple[str, ...]
    pairs: tuple[tuple[str, str], ...]
    provider_configs: tuple[str, ...] = ()
    corpus_backend: str = "native"
    exclude_tags: tuple[str, ...] = ()


def validation_plan_declaration_from_config(
    path: Path, content: bytes | None = None
) -> ValidationPlanDeclaration:
    """Parse a strict matrix plan without consulting the surrounding tree."""
    try:
        source = path.read_bytes() if content is None else content
        value = json.loads(source.decode("utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot read validation plan {path}: {error}") from error
    if not isinstance(value, dict):
        raise ValidationError(f"validation plan {path}: expected a JSON object")
    required = {"version", "adapterConfigs", "pairs"}
    optional = {"providerConfigs", "corpusBackend", "excludeTags"}
    missing = sorted(required - value.keys())
    unknown = sorted(value.keys() - required - optional)
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
    if len(set(raw_configs)) != len(raw_configs):
        raise ValidationError(
            f"validation plan {path}: duplicate adapterConfigs"
        )

    raw_provider_configs = value.get("providerConfigs", [])
    if not isinstance(raw_provider_configs, list) or not all(
        isinstance(config, str) and config for config in raw_provider_configs
    ):
        raise ValidationError(
            f"validation plan {path}: providerConfigs must be a path array"
        )
    if len(set(raw_provider_configs)) != len(raw_provider_configs):
        raise ValidationError(
            f"validation plan {path}: duplicate providerConfigs"
        )

    corpus_backend = validate_backend_name(
        value.get("corpusBackend", "native"),
        f"validation plan {path} corpusBackend",
    )

    raw_exclude_tags = value.get("excludeTags", [])
    if not isinstance(raw_exclude_tags, list) or not all(
        isinstance(tag, str) and tag for tag in raw_exclude_tags
    ):
        raise ValidationError(
            f"validation plan {path}: excludeTags must be a string array"
        )
    if raw_exclude_tags != sorted(set(raw_exclude_tags)):
        raise ValidationError(
            f"validation plan {path}: excludeTags must be sorted and unique"
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
    return ValidationPlanDeclaration(
        tuple(raw_configs),
        tuple(pairs),
        tuple(raw_provider_configs),
        corpus_backend,
        tuple(raw_exclude_tags),
    )


def validation_plan_from_config(
    path: Path, content: bytes | None = None
) -> ValidationPlan:
    """Load a strict matrix plan, resolving config paths beside the plan."""
    declaration = validation_plan_declaration_from_config(path, content)

    def resolve(config: str) -> Path:
        candidate = Path(config)
        return (
            candidate if candidate.is_absolute() else path.parent / candidate
        ).resolve()

    adapter_configs = tuple(
        resolve(config) for config in declaration.adapter_configs
    )
    if len(set(adapter_configs)) != len(adapter_configs):
        raise ValidationError(
            f"validation plan {path}: duplicate adapterConfigs"
        )
    provider_configs = tuple(
        resolve(config) for config in declaration.provider_configs
    )
    if len(set(provider_configs)) != len(provider_configs):
        raise ValidationError(
            f"validation plan {path}: duplicate providerConfigs"
        )
    return ValidationPlan(
        adapter_configs,
        declaration.pairs,
        provider_configs,
        declaration.corpus_backend,
        declaration.exclude_tags,
    )


def validate_control_plane_inputs(
    inputs: tuple[ValidationInput, ...] | list[ValidationInput],
    backend_names: list[str],
    pair_names: list[tuple[str, str]],
    products: list[ValidationProduct],
    bundles: list[ProductBundle],
    consumers: list[ProductConsumer],
    descriptors: list[dict] | None = None,
    selected_cases: list[str] | None = None,
) -> dict[str, ExternalCommandAdapter]:
    """Close retained configs over the matrix claims they authorized."""
    plan_inputs = [
        item for item in inputs if item.kind == "validation-plan"
    ]
    provider_inputs = [
        item for item in inputs if item.kind == "provider-config"
    ]
    adapter_inputs = [
        item for item in inputs if item.kind == "adapter-config"
    ]
    control_inputs = [
        item
        for item in inputs
        if item.kind
        in {"validation-plan", "provider-config", "adapter-config"}
    ]
    if len(plan_inputs) > 1:
        raise ValidationError(
            "validation control plane contains multiple plans"
        )
    expected_kinds = (
        (["validation-plan"] if plan_inputs else [])
        + ["provider-config"] * len(provider_inputs)
        + ["adapter-config"] * len(adapter_inputs)
    )
    if [item.kind for item in control_inputs] != expected_kinds:
        raise ValidationError(
            "validation control-plane inputs are not in canonical order"
        )
    control_contents: dict[tuple[str, str], bytes] = {}
    for item in control_inputs:
        content = item.content
        if content is None:
            raise ValidationError(
                f"validation control-plane input has no retained content: "
                f"{item.kind}:{item.name}"
            )
        if sha256_bytes(content) != item.sha256:
            raise ValidationError(
                f"validation control-plane input content disagrees with "
                f"SHA-256: {item.kind}:{item.name}"
            )
        control_contents[(item.kind, item.name)] = content

    provider_configs: dict[str, ExternalProductProvider] = {}
    for item in provider_inputs:
        provider = external_product_provider_from_config(
            Path(item.name),
            control_contents[(item.kind, item.name)],
        )
        if provider.name in provider_configs:
            raise ValidationError(
                "validation control plane contains duplicate provider config: "
                f"{provider.name}"
            )
        provider_configs[provider.name] = provider
    bundle_by_provider = {bundle.provider: bundle for bundle in bundles}
    if set(provider_configs) != set(bundle_by_provider):
        raise ValidationError(
            "retained provider configs disagree with product bundles"
        )
    for provider_name, provider in provider_configs.items():
        bundle = bundle_by_provider[provider_name]
        manifests = [
            product
            for product in products
            if product.backend == provider_name
            and product.kind == RESERVED_PRODUCT_KIND
        ]
        if provider.contract != bundle.contract:
            raise ValidationError(
                f"retained provider config contract disagrees with bundle: "
                f"{provider_name}"
            )
        if (
            len(manifests) != 1
            or manifests[0].name != provider.bundle_manifest
        ):
            raise ValidationError(
                f"retained provider config bundle manifest disagrees with "
                f"products: {provider_name}"
            )

    adapter_configs: dict[str, ExternalCommandAdapter] = {}
    for item in adapter_inputs:
        adapter = external_adapter_from_config(
            Path(item.name),
            control_contents[(item.kind, item.name)],
        )
        if adapter.name in adapter_configs:
            raise ValidationError(
                "validation control plane contains duplicate adapter config: "
                f"{adapter.name}"
            )
        adapter_configs[adapter.name] = adapter
    consumer_by_backend = {
        consumer.backend: consumer for consumer in consumers
    }
    if len(consumer_by_backend) != len(consumers):
        raise ValidationError(
            "validation control plane contains duplicate product consumers"
        )
    if not set(consumer_by_backend) <= set(adapter_configs):
        raise ValidationError(
            "retained adapter configs omit a product consumer"
        )
    for backend, adapter in adapter_configs.items():
        if backend not in backend_names:
            continue
        requirement = adapter.product_provider
        consumer = consumer_by_backend.get(backend)
        if requirement is None:
            if consumer is not None:
                raise ValidationError(
                    f"retained adapter config omits product provider: {backend}"
                )
            continue
        if (
            consumer is None
            or requirement.provider != consumer.provider
            or requirement.contract != consumer.contract
        ):
            raise ValidationError(
                f"retained adapter config product provider disagrees with "
                f"matrix consumer: {backend}"
            )

    if plan_inputs:
        plan_input = plan_inputs[0]
        plan = validation_plan_declaration_from_config(
            Path(plan_input.name),
            control_contents[(plan_input.kind, plan_input.name)],
        )
        if list(plan.pairs) != pair_names:
            raise ValidationError(
                "retained validation plan pairs disagree with matrix"
            )
        if (
            len(plan.provider_configs) != len(provider_inputs)
            or len(plan.adapter_configs) != len(adapter_inputs)
        ):
            raise ValidationError(
                "retained validation plan config counts disagree with inputs"
            )
        if [PurePosixPath(path).name for path in plan.provider_configs] != [
            PurePosixPath(item.name).name for item in provider_inputs
        ] or [PurePosixPath(path).name for path in plan.adapter_configs] != [
            PurePosixPath(item.name).name for item in adapter_inputs
        ]:
            raise ValidationError(
                "retained validation plan config paths disagree with inputs"
            )
        if plan.exclude_tags:
            if descriptors is None or selected_cases is None:
                raise ValidationError(
                    "retained validation plan exclusions have no corpus selection"
                )
            descriptors_by_id = {
                descriptor["id"]: descriptor for descriptor in descriptors
            }
            excluded_selected = sorted(
                case_id
                for case_id in selected_cases
                if any(
                    tag in descriptors_by_id[case_id]["tags"]
                    for tag in plan.exclude_tags
                )
            )
            if excluded_selected:
                raise ValidationError(
                    "retained validation plan selected excluded case(s): "
                    + ", ".join(excluded_selected)
                )
    return adapter_configs


def verify_execution_file_access_evidence(
    reports: dict[str, dict],
    traces: dict[str, ValidationArtifact],
    adapters: dict[str, ExternalCommandAdapter],
    backend_names: list[str],
    tools: list[ValidationTool],
    bundles: list[ProductBundle],
    consumers: list[ProductConsumer],
    receipts: list[ProductReceipt],
) -> None:
    configured = {
        backend: adapter.execution_file_access_recorder
        for backend, adapter in adapters.items()
        if backend in backend_names
        and adapter.execution_file_access_recorder is not None
    }
    recorder_tools = {
        tool.backend: tool
        for tool in tools
        if tool.kind == EXECUTION_FILE_ACCESS_RECORDER_KIND
    }
    if (
        len(recorder_tools)
        != sum(
            tool.kind == EXECUTION_FILE_ACCESS_RECORDER_KIND
            for tool in tools
        )
        or set(configured) != set(recorder_tools)
        or set(configured) != set(reports)
        or set(configured) != set(traces)
    ):
        raise ValidationError(
            "execution file-access configs, tools, reports, and traces disagree"
        )
    bundle_by_provider = {bundle.provider: bundle for bundle in bundles}
    consumer_by_backend = {
        consumer.backend: consumer for consumer in consumers
    }
    receipts_by_backend: dict[str, list[ProductReceipt]] = {}
    for receipt in receipts:
        receipts_by_backend.setdefault(receipt.backend, []).append(receipt)

    for backend, declaration in configured.items():
        if declaration is None:
            raise ValidationError(
                "execution file-access config lost its recorder"
            )
        tool = recorder_tools[backend]
        if (tool.kind, tool.name) != (
            declaration.kind,
            declaration.name,
        ):
            raise ValidationError(
                "execution file-access recorder tool disagrees with config"
            )
        consumer = consumer_by_backend.get(backend)
        if consumer is None:
            raise ValidationError(
                "execution file-access recorder has no product consumer"
            )
        bundle = bundle_by_provider[consumer.provider]
        report = reports[backend]
        if not isinstance(report, dict) or set(report) != {
            "version",
            "backend",
            "recorder",
            "provider",
            "bundleSha256",
            "trace",
            "receiptCount",
            "products",
            "productCount",
            "accessCount",
        }:
            raise ValidationError(
                "execution-file-access artifact is malformed"
            )
        trace_artifact = traces[backend]
        trace_reference = report["trace"]
        if (
            report["version"] != PROTOCOL_VERSION
            or isinstance(report["version"], bool)
            or report["backend"] != backend
            or report["recorder"] != tool.to_json()
            or report["provider"] != consumer.provider
            or report["bundleSha256"] != bundle.bundle_sha256
            or not isinstance(trace_reference, dict)
            or set(trace_reference) != {"name", "sha256"}
            or trace_reference["name"] != trace_artifact.name
            or trace_reference["sha256"] != trace_artifact.sha256
        ):
            raise ValidationError(
                "execution-file-access artifact disagrees with evidence"
            )
        parsed_accesses = parse_file_access_trace(
            trace_artifact.content,
            f"retained {backend} execution file-access trace",
        )
        backend_receipts = receipts_by_backend.get(backend, [])
        expected_products = {
            (product.backend, product.kind, product.name, product.sha256): product
            for receipt in backend_receipts
            for product in receipt.products
        }
        raw_products = report["products"]
        if not isinstance(raw_products, list):
            raise ValidationError(
                "execution-file-access products are malformed"
            )
        checked_products: list[tuple[str, str, str, str]] = []
        observed_paths: set[str] = set()
        for item in raw_products:
            if not isinstance(item, dict) or set(item) != {
                "backend",
                "kind",
                "name",
                "sha256",
                "path",
                "accesses",
            }:
                raise ValidationError(
                    "execution-file-access product is malformed"
                )
            if not all(
                isinstance(item[field], str)
                for field in ("backend", "kind", "name", "sha256")
            ):
                raise ValidationError(
                    "execution-file-access product identity is malformed"
                )
            key = (
                item["backend"],
                item["kind"],
                item["name"],
                item["sha256"],
            )
            product = expected_products.get(key)
            path = item["path"]
            accesses = item["accesses"]
            if (
                product is None
                or not isinstance(path, str)
                or not Path(path).is_absolute()
                or os.path.normpath(path) != path
                or path in observed_paths
                or not isinstance(accesses, list)
                or not all(isinstance(access, str) for access in accesses)
                or accesses != sorted(set(accesses))
                or "read" not in accesses
                or list(parsed_accesses.get(path, ())) != accesses
            ):
                raise ValidationError(
                    "execution-file-access product disagrees with trace"
                )
            expected_suffix = (
                consumer.provider,
                *PurePosixPath(product.name).parts,
            )
            if tuple(Path(path).parts[-len(expected_suffix):]) != expected_suffix:
                raise ValidationError(
                    "execution-file-access product path disagrees with provider"
                )
            observed_paths.add(path)
            checked_products.append(key)
        expected_keys = sorted(expected_products)
        if (
            checked_products != expected_keys
            or report["receiptCount"] != len(backend_receipts)
            or isinstance(report["receiptCount"], bool)
            or report["productCount"] != len(expected_keys)
            or isinstance(report["productCount"], bool)
            or report["accessCount"] != len(parsed_accesses)
            or isinstance(report["accessCount"], bool)
        ):
            raise ValidationError(
                "execution-file-access counts or product inventory disagree"
            )


def validation_coverage_report(
    selected_cases: list[str],
    backend_names: list[str],
    pairs: list[tuple[str, str, int, int, int]],
    finding_backends: list[str | None],
    bundles: list[ProductBundle],
    consumers: list[ProductConsumer],
    receipts: list[ProductReceipt],
    result_records: dict[tuple[str, str], dict],
    execution_access_reports: dict[str, dict],
) -> dict:
    """Build the canonical, evidence-derived validation coverage summary."""
    def is_success(record: dict, backend: str) -> bool:
        _, outcome = checked_record(record, backend)
        if "success" not in outcome:
            return False
        success_observation(record)
        return True

    backend_comparisons = {
        backend: {"compared": 0, "equal": 0} for backend in backend_names
    }
    pair_coverage: list[dict[str, object]] = []
    for reference, candidate, compared, equal, finding_count in pairs:
        pair_coverage.append(
            {
                "reference": reference,
                "candidate": candidate,
                "selectedCaseCount": len(selected_cases),
                "comparedCaseCount": compared,
                "equalCaseCount": equal,
                "findingCount": finding_count,
            }
        )
        for backend in (reference, candidate):
            backend_comparisons[backend]["compared"] += compared
            backend_comparisons[backend]["equal"] += equal

    backend_coverage: list[dict[str, object]] = []
    successful_backend_results = 0
    for backend in backend_names:
        records = [
            record
            for (case_id, record_backend), record in result_records.items()
            if record_backend == backend and case_id in selected_cases
        ]
        success_count = sum(int(is_success(record, backend)) for record in records)
        successful_backend_results += success_count
        backend_coverage.append(
            {
                "backend": backend,
                "selectedCaseCount": len(selected_cases),
                "resultCaseCount": len(records),
                "successfulCaseCount": success_count,
                "comparisonCount": backend_comparisons[backend]["compared"],
                "equalComparisonCount": backend_comparisons[backend]["equal"],
                "findingCount": finding_backends.count(backend),
            }
        )

    consumer_counts = {bundle.provider: 0 for bundle in bundles}
    for consumer in consumers:
        consumer_counts[consumer.provider] += 1
    provider_coverage = [
        {
            "provider": bundle.provider,
            "bundleCaseCount": len(bundle.case_products),
            "bundleProductCount": len(bundle.products),
            "consumerCount": consumer_counts[bundle.provider],
            "findingCount": finding_backends.count(bundle.provider),
        }
        for bundle in bundles
    ]

    consumer_coverage: list[dict[str, object]] = []
    for consumer in consumers:
        backend_receipts = [
            receipt for receipt in receipts if receipt.backend == consumer.backend
        ]
        receipted_products = {
            (product.backend, product.kind, product.name, product.sha256)
            for receipt in backend_receipts
            for product in receipt.products
        }
        access_report = execution_access_reports.get(consumer.backend)
        if access_report is None:
            execution_access = {
                "recorded": False,
                "recorder": None,
                "openedReceiptedProductCount": 0,
                "traceAccessCount": 0,
            }
        else:
            recorder = access_report.get("recorder")
            product_count = access_report.get("productCount")
            access_count = access_report.get("accessCount")
            if (
                not isinstance(recorder, dict)
                or not isinstance(recorder.get("name"), str)
                or not isinstance(product_count, int)
                or isinstance(product_count, bool)
                or product_count < 0
                or not isinstance(access_count, int)
                or isinstance(access_count, bool)
                or access_count < 0
            ):
                raise ValidationError(
                    f"cannot summarize malformed {consumer.backend} "
                    "execution file-access report"
                )
            execution_access = {
                "recorded": True,
                "recorder": recorder["name"],
                "openedReceiptedProductCount": product_count,
                "traceAccessCount": access_count,
            }
        consumer_coverage.append(
            {
                "backend": consumer.backend,
                "provider": consumer.provider,
                "selectedCaseCount": len(selected_cases),
                "receiptCaseCount": len(backend_receipts),
                "receiptedProductReferenceCount": sum(
                    len(receipt.products) for receipt in backend_receipts
                ),
                "uniqueReceiptedProductCount": len(receipted_products),
                "executionAccess": execution_access,
            }
        )

    assigned_finding_owners = {
        *backend_names,
        *(bundle.provider for bundle in bundles),
    }
    return {
        "selectedCaseCount": len(selected_cases),
        "expectedBackendResultCount": len(selected_cases) * len(backend_names),
        "backendResultCount": len(result_records),
        "successfulBackendResultCount": successful_backend_results,
        "findingCount": len(finding_backends),
        "unassignedFindingCount": sum(
            int(owner not in assigned_finding_owners)
            for owner in finding_backends
        ),
        "backends": backend_coverage,
        "pairs": pair_coverage,
        "providers": provider_coverage,
        "consumers": consumer_coverage,
    }


def render_validation_coverage(coverage: dict) -> list[str]:
    """Render a verified canonical coverage report for humans."""
    lines = [
        "coverage results: "
        f"{coverage['successfulBackendResultCount']}/"
        f"{coverage['backendResultCount']} successful, "
        f"{coverage['backendResultCount']}/"
        f"{coverage['expectedBackendResultCount']} present, "
        f"findings {coverage['findingCount']} "
        f"({coverage['unassignedFindingCount']} unassigned)"
    ]
    for backend in coverage["backends"]:
        lines.append(
            f"coverage backend {backend['backend']}: "
            f"results {backend['resultCaseCount']}/"
            f"{backend['selectedCaseCount']}, "
            f"successful {backend['successfulCaseCount']}, "
            f"comparisons {backend['equalComparisonCount']}/"
            f"{backend['comparisonCount']} equal, "
            f"findings {backend['findingCount']}"
        )
    for pair in coverage["pairs"]:
        lines.append(
            f"coverage pair {pair['reference']} -> {pair['candidate']}: "
            f"compared {pair['comparedCaseCount']}/"
            f"{pair['selectedCaseCount']}, "
            f"equal {pair['equalCaseCount']}, "
            f"findings {pair['findingCount']}"
        )
    for provider in coverage["providers"]:
        lines.append(
            f"coverage provider {provider['provider']}: "
            f"bundle cases {provider['bundleCaseCount']}, "
            f"products {provider['bundleProductCount']}, "
            f"consumers {provider['consumerCount']}, "
            f"findings {provider['findingCount']}"
        )
    for consumer in coverage["consumers"]:
        access = consumer["executionAccess"]
        if access["recorded"]:
            access_text = (
                f", opened {access['openedReceiptedProductCount']}/"
                f"{consumer['uniqueReceiptedProductCount']} unique products "
                f"with {access['recorder']} "
                f"({access['traceAccessCount']} trace paths)"
            )
        else:
            access_text = ", execution access not recorded"
        lines.append(
            f"coverage consumer {consumer['backend']} <- "
            f"{consumer['provider']}: receipts "
            f"{consumer['receiptCaseCount']}/"
            f"{consumer['selectedCaseCount']}, product references "
            f"{consumer['receiptedProductReferenceCount']}, unique products "
            f"{consumer['uniqueReceiptedProductCount']}{access_text}"
        )
    return lines


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
    tools: tuple[ValidationTool, ...] = (),
    artifacts: tuple[ValidationArtifact, ...] = (),
    build_inputs: tuple[ValidationBuildInput, ...] = (),
    provider_runs: tuple[ProductProviderRun, ...] = (),
    product_consumers: tuple[ProductConsumer, ...] = (),
    product_receipts: tuple[ProductReceipt, ...] = (),
) -> Path:
    context.out_dir.mkdir(parents=True, exist_ok=True)
    provider_runs = tuple(
        sorted(provider_runs, key=lambda run: run.provider)
    )
    provider_names = [
        validate_backend_name(run.provider, "product provider")
        for run in provider_runs
    ]
    if len(set(provider_names)) != len(provider_names):
        raise ValidationError("validation matrix contains duplicate providers")
    if set(provider_names) & set(backend_names):
        raise ValidationError(
            "validation matrix provider and backend names must be disjoint"
        )
    component_names = [*backend_names, *provider_names]
    bundles = [run.bundle for run in provider_runs]
    for run, bundle in zip(provider_runs, bundles):
        if bundle.provider != run.provider:
            raise ValidationError(
                f"provider run {run.provider} returned bundle for "
                f"{bundle.provider}"
            )
        expected_digest = product_bundle_sha256(
            bundle.provider,
            bundle.contract,
            bundle.products,
            bundle.case_products,
        )
        if bundle.bundle_sha256 != expected_digest:
            raise ValidationError(
                f"product bundle identity mismatch: {bundle.provider}"
            )
    sorted_consumers = sorted(
        product_consumers, key=lambda item: item.backend
    )
    if len({item.backend for item in sorted_consumers}) != len(
        sorted_consumers
    ):
        raise ValidationError("validation matrix contains duplicate consumers")
    bundle_by_provider = {bundle.provider: bundle for bundle in bundles}
    for consumer in sorted_consumers:
        if consumer.backend not in backend_names:
            raise ValidationError(
                f"product consumer names inactive backend: {consumer.backend}"
            )
        bundle = bundle_by_provider.get(consumer.provider)
        if (
            bundle is None
            or consumer.contract != bundle.contract
            or consumer.bundle_sha256 != bundle.bundle_sha256
        ):
            raise ValidationError(
                f"product consumer {consumer.backend} disagrees with provider"
            )
    sorted_receipts = sorted(
        product_receipts, key=lambda item: (item.backend, item.case_id)
    )
    receipt_keys = [
        (receipt.backend, receipt.case_id) for receipt in sorted_receipts
    ]
    if len(set(receipt_keys)) != len(receipt_keys):
        raise ValidationError("validation matrix contains duplicate receipts")
    consumer_by_backend = {
        consumer.backend: consumer for consumer in sorted_consumers
    }
    for receipt in sorted_receipts:
        consumer = consumer_by_backend.get(receipt.backend)
        bundle = bundle_by_provider.get(receipt.provider)
        expected_products = (
            bundle.products_by_case.get(receipt.case_id)
            if bundle is not None
            else None
        )
        if (
            consumer is None
            or receipt.case_id not in context.selected
            or receipt.provider != consumer.provider
            or receipt.bundle_sha256 != consumer.bundle_sha256
            or receipt.products != expected_products
        ):
            raise ValidationError(
                f"product receipt disagrees with provider case binding: "
                f"{receipt.backend}/{receipt.case_id}"
            )
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
    sorted_products = sorted(
        products,
        key=lambda product: (product.backend, product.kind, product.name),
    )
    for product in sorted_products:
        validate_backend_name(product.backend, "validation product backend")
        validate_backend_name(product.kind, "validation product kind")
        checked_relative_posix_path(product.name, "validation product")
        if product.backend not in component_names:
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
    retained_adapters = validate_control_plane_inputs(
        inputs,
        backend_names,
        [
            (result.reference, result.candidate)
            for result in pair_results
        ],
        sorted_products,
        bundles,
        sorted_consumers,
        context.descriptors,
        list(context.selected),
    )
    retained_inputs = retain_validation_inputs(context, inputs)
    retained_products = retain_validation_products(context, sorted_products)
    sorted_tools = sorted(
        tools,
        key=lambda tool: (tool.backend, tool.kind, tool.name),
    )
    for tool in sorted_tools:
        validate_backend_name(tool.backend, "validation tool backend")
        validate_backend_name(tool.kind, "validation tool kind")
        checked_relative_posix_path(tool.name, "validation tool name")
        if tool.backend not in component_names:
            raise ValidationError(
                f"validation tool names inactive backend: {tool.backend}"
            )
        checked_sha256(tool.sha256, "validation tool")
    tool_keys = [(tool.backend, tool.kind, tool.name) for tool in sorted_tools]
    if len(set(tool_keys)) != len(tool_keys):
        raise ValidationError("validation matrix contains duplicate backend tools")
    retained_tools = retain_validation_tools(context, sorted_tools)
    sorted_build_inputs = sorted(
        build_inputs,
        key=lambda item: (item.backend, item.kind, item.name),
    )
    for item in sorted_build_inputs:
        validate_backend_name(
            item.backend, "validation build input backend"
        )
        validate_backend_name(item.kind, "validation build input kind")
        checked_relative_posix_path(
            item.name, "validation build input name"
        )
        if item.backend not in component_names:
            raise ValidationError(
                f"validation build input names inactive backend: "
                f"{item.backend}"
            )
        checked_sha256(item.sha256, "validation build input")
    build_input_keys = [
        (item.backend, item.kind, item.name)
        for item in sorted_build_inputs
    ]
    if len(set(build_input_keys)) != len(build_input_keys):
        raise ValidationError(
            "validation matrix contains duplicate build inputs"
        )
    for backend in component_names:
        backend_inputs = [
            item for item in sorted_build_inputs if item.backend == backend
        ]
        manifests = [
            item
            for item in backend_inputs
            if item.kind == RESERVED_BUILD_INPUT_KIND
        ]
        members = [
            item
            for item in backend_inputs
            if item.kind != RESERVED_BUILD_INPUT_KIND
        ]
        if bool(manifests) != bool(members) or len(manifests) > 1:
            raise ValidationError(
                f"validation build inputs for {backend} require exactly one "
                "manifest"
            )
        if manifests:
            manifest = manifests[0]
            expected = canonical_build_input_manifest_bytes(tuple(members))
            if manifest.content != expected or manifest.sha256 != sha256_bytes(
                expected
            ):
                raise ValidationError(
                    f"validation build input manifest for {backend} "
                    "disagrees with inputs"
                )
    retained_build_inputs = retain_validation_build_inputs(
        context, sorted_build_inputs
    )
    sorted_artifacts = sorted(
        artifacts,
        key=lambda artifact: (artifact.kind, artifact.name),
    )
    coverage_results: dict[tuple[str, str], dict] = {}
    coverage_execution_access: dict[str, dict] = {}
    execution_input_backends: set[str] = set()
    for artifact in sorted_artifacts:
        artifact_backend, artifact_case, _ = validation_artifact_scope(
            artifact.kind,
            artifact.name,
            component_names,
            list(context.selected),
        )
        checked_sha256(artifact.sha256, "validation artifact")
        if artifact.kind == "backend-result":
            if artifact_case is None:
                raise ValidationError("backend-result artifact has no case")
            try:
                record = json.loads(artifact.content.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValidationError(
                    "backend-result artifact is not JSON"
                ) from error
            if not isinstance(record, dict):
                raise ValidationError("backend-result artifact is malformed")
            recorded_case, _ = checked_record(record, artifact_backend)
            if recorded_case != artifact_case:
                raise ValidationError(
                    "backend-result artifact disagrees with its name"
                )
            coverage_results[(artifact_case, artifact_backend)] = record
        elif artifact.kind == "execution-file-access":
            try:
                access_report = json.loads(artifact.content.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValidationError(
                    "execution-file-access artifact is not JSON"
                ) from error
            if not isinstance(access_report, dict):
                raise ValidationError(
                    "execution-file-access artifact is malformed"
                )
            coverage_execution_access[artifact_backend] = access_report
        elif artifact.kind == "execution-input":
            consumer = consumer_by_backend.get(artifact_backend)
            bundle = (
                bundle_by_provider.get(consumer.provider)
                if consumer is not None
                else None
            )
            exposed_products = (
                bundle.products
                if bundle is not None
                else tuple(
                    product
                    for product in sorted_products
                    if product.backend == artifact_backend
                )
            )
            checked_execution_input(
                artifact.content,
                artifact_backend,
                list(context.selected),
                exposed_products,
                bundle,
                f"validation artifact {artifact.name}",
                context.out_dir,
            )
            execution_input_backends.add(artifact_backend)
    artifact_keys = [
        (artifact.kind, artifact.name) for artifact in sorted_artifacts
    ]
    if len(set(artifact_keys)) != len(artifact_keys):
        raise ValidationError("validation matrix contains duplicate artifacts")
    expected_execution_input_backends = {
        backend
        for artifact in sorted_artifacts
        if artifact.kind == "process-stdout"
        for backend, case_id, scope in [
            validation_artifact_scope(
                artifact.kind,
                artifact.name,
                component_names,
                list(context.selected),
            )
        ]
        if (
            case_id is None
            and scope == "execute"
            and backend in retained_adapters
        )
    }
    if not expected_execution_input_backends <= execution_input_backends:
        raise ValidationError(
            "external execution process has no retained execution input"
        )
    retained_artifacts = retain_validation_artifacts(context, sorted_artifacts)
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
        sorted_tools,
        sorted_build_inputs,
        bundles if provider_runs else None,
        sorted_consumers if provider_runs else None,
        sorted_receipts if provider_runs else None,
    )
    matrix_value = {
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
        "tools": retained_tools,
        "buildInputs": retained_build_inputs,
        "artifacts": retained_artifacts,
        "pairs": pairs,
        "findings": [finding.to_json() for finding in findings],
        "coverage": validation_coverage_report(
            list(context.selected),
            backend_names,
            [
                (
                    result.reference,
                    result.candidate,
                    len(result.comparisons),
                    sum(
                        int(comparison["equal"])
                        for comparison in result.comparisons
                    ),
                    len(result.findings),
                )
                for result in pair_results
            ],
            [finding.backend for finding in findings],
            bundles,
            sorted_consumers,
            sorted_receipts,
            coverage_results,
            coverage_execution_access,
        ),
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
            "toolCount": len(sorted_tools),
            "buildInputCount": len(sorted_build_inputs),
            "artifactCount": len(sorted_artifacts),
        },
    }
    if provider_runs:
        matrix_value["providers"] = provider_names
        matrix_value["productBundles"] = [
            bundle.to_json() for bundle in bundles
        ]
        matrix_value["productConsumers"] = [
            consumer.to_json() for consumer in sorted_consumers
        ]
        matrix_value["productReceipts"] = [
            receipt.to_json() for receipt in sorted_receipts
        ]
        matrix_value["summary"].update(
            {
                "providerCount": len(provider_names),
                "bundleCount": len(bundles),
                "productConsumerCount": len(sorted_consumers),
                "productReceiptCount": len(sorted_receipts),
            }
        )
    matrix_content = (
        json.dumps(matrix_value, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")
    (context.out_dir / "matrix.json").write_bytes(matrix_content)
    return write_evidence_manifest(
        context.out_dir,
        matrix_content,
        run_sha256,
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


def verify_matrix_artifact(
    path: Path, report_root: Path | None = None
) -> dict:
    """Verify retained run evidence, semantic comparisons, and identities."""
    if path.is_symlink() or not path.is_file():
        raise ValidationError(f"validation matrix is not a regular file: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot read validation matrix {path}: {error}") from error
    legacy_fields = {
        "version",
        "identity",
        "selectedCases",
        "backends",
        "inputs",
        "products",
        "tools",
        "buildInputs",
        "artifacts",
        "pairs",
        "findings",
        "coverage",
        "summary",
    }
    provider_fields = {
        "providers", "productBundles", "productConsumers", "productReceipts"
    }
    if not isinstance(value, dict) or set(value) not in (
        legacy_fields,
        legacy_fields | provider_fields,
    ):
        raise ValidationError("validation matrix has malformed top-level fields")
    has_providers = set(value) == legacy_fields | provider_fields
    if (
        not isinstance(value["version"], int)
        or isinstance(value["version"], bool)
        or value["version"] != PROTOCOL_VERSION
    ):
        raise ValidationError("validation matrix has unsupported version")
    report_root = path.parent if report_root is None else report_root

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
    raw_providers = value.get("providers", [])
    if not isinstance(raw_providers, list):
        raise ValidationError("validation matrix has malformed providers")
    checked_providers = [
        validate_backend_name(provider, "validation matrix provider")
        for provider in raw_providers
    ]
    if (
        len(set(checked_providers)) != len(checked_providers)
        or checked_providers != sorted(checked_providers)
    ):
        raise ValidationError(
            "validation matrix providers are not sorted and unique"
        )
    if set(checked_backends) & set(checked_providers):
        raise ValidationError(
            "validation matrix provider and backend names overlap"
        )
    checked_components = [*checked_backends, *checked_providers]

    raw_inputs = value["inputs"]
    if not isinstance(raw_inputs, list) or not raw_inputs:
        raise ValidationError("validation matrix has malformed inputs")
    inputs: list[ValidationInput] = []
    input_contents: dict[tuple[str, str], bytes] = {}
    corpus_content: bytes | None = None
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
        input_content = verify_evidence_file(
            report_root,
            item["artifact"],
            digest,
            f"validation input {kind}:{name}",
        )
        if index == 0 and (kind != "corpus" or name != "corpus.json"):
            raise ValidationError("first validation input must be corpus.json")
        if index == 0:
            corpus_content = input_content
        input_contents[(kind, name)] = input_content
        inputs.append(ValidationInput(kind, name, digest, input_content))
    input_keys = [(item.kind, item.name) for item in inputs]
    if len(set(input_keys)) != len(input_keys):
        raise ValidationError("validation matrix has duplicate inputs")
    if corpus_content is None:
        raise ValidationError("validation matrix has no retained corpus")
    try:
        corpus = json.loads(corpus_content.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError("retained validation corpus is not JSON") from error
    if (
        not isinstance(corpus, dict)
        or set(corpus) != {"version", "cases"}
        or corpus["version"] != PROTOCOL_VERSION
        or isinstance(corpus["version"], bool)
        or not isinstance(corpus["cases"], list)
    ):
        raise ValidationError("retained validation corpus is malformed")
    corpus_cases: dict[str, dict] = {}
    for descriptor in corpus["cases"]:
        if not isinstance(descriptor, dict):
            raise ValidationError("retained validation corpus is malformed")
        case_id = validate_backend_name(
            descriptor.get("id"), "retained validation corpus case ID"
        )
        if case_id in corpus_cases:
            raise ValidationError("retained validation corpus has duplicate cases")
        corpus_cases[case_id] = descriptor
    if any(case_id not in corpus_cases for case_id in selected_cases):
        raise ValidationError("validation selection names unknown corpus case")

    raw_products = value["products"]
    if not isinstance(raw_products, list):
        raise ValidationError("validation matrix has malformed products")
    products: list[ValidationProduct] = []
    product_contents: dict[tuple[str, str, str], bytes] = {}
    for item in raw_products:
        if not isinstance(item, dict) or set(item) != {
            "backend", "kind", "name", "sha256", "artifact"
        }:
            raise ValidationError("validation matrix has malformed product")
        backend = validate_backend_name(item["backend"], "validation product backend")
        kind = validate_backend_name(item["kind"], "validation product kind")
        name = checked_relative_posix_path(item["name"], "validation product name")
        digest = checked_sha256(item["sha256"], "validation product")
        if backend not in checked_components:
            raise ValidationError("validation product names inactive backend")
        expected_artifact = f"evidence/products/{digest}"
        if item["artifact"] != expected_artifact:
            raise ValidationError("validation product has noncanonical artifact path")
        product_content = verify_evidence_file(
            report_root,
            item["artifact"],
            digest,
            f"validation product {backend}:{kind}:{name}",
        )
        product_contents[(backend, kind, name)] = product_content
        products.append(ValidationProduct(backend, kind, name, digest))
    product_keys = [
        (product.backend, product.kind, product.name) for product in products
    ]
    if len(set(product_keys)) != len(product_keys):
        raise ValidationError("validation matrix has duplicate products")
    if product_keys != sorted(product_keys):
        raise ValidationError("validation matrix products are not sorted")
    for backend in checked_components:
        manifests = [
            product
            for product in products
            if product.backend == backend
            and product.kind == RESERVED_PRODUCT_KIND
        ]
        if len(manifests) > 1:
            raise ValidationError(
                "validation matrix has multiple product manifests for a backend"
            )
        if not manifests:
            continue
        manifest = manifests[0]
        declarations = product_declarations_from_manifest(
            product_contents[(manifest.backend, manifest.kind, manifest.name)],
            f"retained {backend} product manifest",
        )
        declared = {(item.kind, item.path) for item in declarations}
        retained = {
            (product.kind, product.name)
            for product in products
            if product.backend == backend
            and product.kind != RESERVED_PRODUCT_KIND
        }
        if declared != retained:
            raise ValidationError(
                f"retained {backend} product manifest disagrees with matrix products"
            )

    raw_bundles = value.get("productBundles", [])
    if not isinstance(raw_bundles, list):
        raise ValidationError("validation matrix has malformed productBundles")
    bundles = [
        product_bundle_from_json(
            item,
            checked_providers,
            products,
            selected_cases,
            f"validation product bundle {index}",
        )
        for index, item in enumerate(raw_bundles)
    ]
    if (
        [bundle.provider for bundle in bundles] != checked_providers
        or len(bundles) != len(checked_providers)
    ):
        raise ValidationError(
            "validation product bundles disagree with providers"
        )
    bundle_by_provider = {bundle.provider: bundle for bundle in bundles}
    for bundle in bundles:
        manifests = [
            product for product in products
            if product.backend == bundle.provider
            and product.kind == RESERVED_PRODUCT_KIND
        ]
        if len(manifests) != 1:
            raise ValidationError(
                f"provider {bundle.provider} requires one bundle manifest"
            )
        manifest = manifests[0]
        reconstructed = product_bundle_from_manifest(
            bundle.provider,
            bundle.contract,
            product_contents[
                (manifest.backend, manifest.kind, manifest.name)
            ],
            tuple(
                product for product in products
                if product.backend == bundle.provider
            ),
            selected_cases,
            f"retained {bundle.provider} product bundle manifest",
        )
        if reconstructed != bundle:
            raise ValidationError(
                f"retained {bundle.provider} bundle disagrees with matrix"
            )

    raw_consumers = value.get("productConsumers", [])
    if not isinstance(raw_consumers, list):
        raise ValidationError("validation matrix has malformed productConsumers")
    product_consumers: list[ProductConsumer] = []
    for index, item in enumerate(raw_consumers):
        consumer_context = f"validation product consumer {index}"
        if not isinstance(item, dict) or set(item) != {
            "backend", "provider", "contract", "bundleSha256"
        }:
            raise ValidationError(f"{consumer_context}: malformed consumer")
        backend = validate_backend_name(item["backend"], consumer_context)
        provider = validate_backend_name(item["provider"], consumer_context)
        contract = product_contract_from_json(
            item["contract"], f"{consumer_context} contract"
        )
        bundle_sha256 = checked_sha256(
            item["bundleSha256"], f"{consumer_context} bundle"
        )
        bundle = bundle_by_provider.get(provider)
        if (
            backend not in checked_backends
            or bundle is None
            or contract != bundle.contract
            or bundle_sha256 != bundle.bundle_sha256
        ):
            raise ValidationError(
                f"{consumer_context}: disagrees with backend or provider"
            )
        product_consumers.append(
            ProductConsumer(backend, provider, contract, bundle_sha256)
        )
    if (
        [consumer.backend for consumer in product_consumers]
        != sorted(consumer.backend for consumer in product_consumers)
        or len({consumer.backend for consumer in product_consumers})
        != len(product_consumers)
    ):
        raise ValidationError(
            "validation product consumers are not sorted and unique"
        )
    if has_providers != bool(checked_providers):
        raise ValidationError(
            "validation matrix provider schema is empty or incomplete"
        )
    if checked_providers and {
        consumer.provider for consumer in product_consumers
    } != set(checked_providers):
        raise ValidationError(
            "validation matrix contains an unused product provider"
        )

    raw_receipts = value.get("productReceipts", [])
    if not isinstance(raw_receipts, list):
        raise ValidationError("validation matrix has malformed productReceipts")
    product_receipts: list[ProductReceipt] = []
    consumer_by_backend = {
        consumer.backend: consumer for consumer in product_consumers
    }
    for index, item in enumerate(raw_receipts):
        receipt_context = f"validation product receipt {index}"
        if not isinstance(item, dict):
            raise ValidationError(f"{receipt_context}: malformed receipt")
        backend = validate_backend_name(
            item.get("backend"), f"{receipt_context} backend"
        )
        case_id = validate_backend_name(
            item.get("caseId"), f"{receipt_context} case"
        )
        provider = validate_backend_name(
            item.get("provider"), f"{receipt_context} provider"
        )
        bundle = bundle_by_provider.get(provider)
        consumer = consumer_by_backend.get(backend)
        receipt_products = (
            bundle.products_by_case.get(case_id)
            if bundle is not None
            else None
        )
        if bundle is None or consumer is None or receipt_products is None:
            raise ValidationError(
                f"{receipt_context}: names inactive consumer, provider, or case"
            )
        receipt = ProductReceipt(
            backend,
            case_id,
            provider,
            bundle.bundle_sha256,
            receipt_products,
        )
        if item != receipt.to_json() or consumer.provider != provider:
            raise ValidationError(
                f"{receipt_context}: disagrees with provider case binding"
            )
        product_receipts.append(receipt)
    if [
        (receipt.backend, receipt.case_id) for receipt in product_receipts
    ] != sorted(
        (receipt.backend, receipt.case_id) for receipt in product_receipts
    ) or len({
        (receipt.backend, receipt.case_id) for receipt in product_receipts
    }) != len(product_receipts):
        raise ValidationError(
            "validation product receipts are not sorted and unique"
        )

    raw_tools = value["tools"]
    if not isinstance(raw_tools, list):
        raise ValidationError("validation matrix has malformed tools")
    tools: list[ValidationTool] = []
    for item in raw_tools:
        if not isinstance(item, dict) or set(item) != {
            "backend", "kind", "name", "sha256", "artifact"
        }:
            raise ValidationError("validation matrix has malformed tool")
        backend = validate_backend_name(item["backend"], "validation tool backend")
        kind = validate_backend_name(item["kind"], "validation tool kind")
        name = checked_relative_posix_path(item["name"], "validation tool name")
        digest = checked_sha256(item["sha256"], "validation tool")
        if backend not in checked_components:
            raise ValidationError("validation tool names inactive backend")
        expected_artifact = f"evidence/tools/{digest}"
        if item["artifact"] != expected_artifact:
            raise ValidationError("validation tool has noncanonical artifact path")
        verify_evidence_file(
            report_root,
            item["artifact"],
            digest,
            f"validation tool {backend}:{kind}:{name}",
        )
        tools.append(ValidationTool(backend, kind, name, digest))
    tool_keys = [(tool.backend, tool.kind, tool.name) for tool in tools]
    if len(set(tool_keys)) != len(tool_keys):
        raise ValidationError("validation matrix has duplicate tools")
    if tool_keys != sorted(tool_keys):
        raise ValidationError("validation matrix tools are not sorted")

    raw_build_inputs = value["buildInputs"]
    if not isinstance(raw_build_inputs, list):
        raise ValidationError("validation matrix has malformed buildInputs")
    build_inputs: list[ValidationBuildInput] = []
    build_input_contents: dict[tuple[str, str, str], bytes] = {}
    for item in raw_build_inputs:
        if not isinstance(item, dict) or set(item) != {
            "backend", "kind", "name", "sha256", "artifact"
        }:
            raise ValidationError(
                "validation matrix has malformed build input"
            )
        backend = validate_backend_name(
            item["backend"], "validation build input backend"
        )
        kind = validate_backend_name(
            item["kind"], "validation build input kind"
        )
        name = checked_relative_posix_path(
            item["name"], "validation build input name"
        )
        digest = checked_sha256(item["sha256"], "validation build input")
        if backend not in checked_components:
            raise ValidationError(
                "validation build input names inactive backend"
            )
        expected_artifact = f"evidence/build-inputs/{digest}"
        if item["artifact"] != expected_artifact:
            raise ValidationError(
                "validation build input has noncanonical artifact path"
            )
        content = verify_evidence_file(
            report_root,
            item["artifact"],
            digest,
            f"validation build input {backend}:{kind}:{name}",
        )
        if kind == RESERVED_BUILD_INPUT_KIND:
            build_input_contents[(backend, kind, name)] = content
        build_inputs.append(
            ValidationBuildInput(backend, kind, name, digest)
        )
    build_input_keys = [
        (item.backend, item.kind, item.name) for item in build_inputs
    ]
    if len(set(build_input_keys)) != len(build_input_keys):
        raise ValidationError("validation matrix has duplicate build inputs")
    if build_input_keys != sorted(build_input_keys):
        raise ValidationError("validation matrix build inputs are not sorted")
    for backend in checked_components:
        backend_inputs = [
            item for item in build_inputs if item.backend == backend
        ]
        manifests = [
            item
            for item in backend_inputs
            if item.kind == RESERVED_BUILD_INPUT_KIND
        ]
        members = tuple(
            item
            for item in backend_inputs
            if item.kind != RESERVED_BUILD_INPUT_KIND
        )
        if bool(manifests) != bool(members) or len(manifests) > 1:
            raise ValidationError(
                f"validation build inputs for {backend} require exactly one "
                "manifest"
            )
        if manifests:
            manifest = manifests[0]
            declared = build_inputs_from_canonical_manifest(
                backend,
                build_input_contents[
                    (manifest.backend, manifest.kind, manifest.name)
                ],
                f"retained {backend} build input manifest",
            )
            if declared != members:
                raise ValidationError(
                    f"retained {backend} build input manifest disagrees "
                    "with matrix build inputs"
                )

    raw_artifacts = value["artifacts"]
    if not isinstance(raw_artifacts, list):
        raise ValidationError("validation matrix has malformed artifacts")
    artifacts: list[ValidationArtifact] = []
    result_records: dict[tuple[str, str], dict] = {}
    determinism_backends: set[str] = set()
    determinism_attempt_counts: dict[str, int] = {}
    determinism_attempts: dict[
        str, list[tuple[list[dict[str, str]], list[dict[str, str]]]]
    ] = {}
    file_access_reports: dict[str, dict] = {}
    file_access_traces: dict[
        tuple[str, str], ValidationArtifact
    ] = {}
    execution_access_reports: dict[str, dict] = {}
    execution_access_traces: dict[str, ValidationArtifact] = {}
    execution_inputs: dict[str, dict] = {}
    replay_reports: dict[str, dict] = {}
    replay_traces: dict[str, ValidationArtifact] = {}
    replay_statuses: dict[str, ValidationArtifact] = {}
    replay_manifests: dict[str, ValidationArtifact] = {}
    stdout_scopes: set[tuple[str, str | None, str]] = set()
    stderr_scopes: set[tuple[str, str | None, str]] = set()
    for item in raw_artifacts:
        if not isinstance(item, dict) or set(item) != {
            "kind", "name", "sha256", "artifact"
        }:
            raise ValidationError("validation matrix has malformed artifact")
        kind = validate_backend_name(item["kind"], "validation artifact kind")
        name = checked_relative_posix_path(
            item["name"], "validation artifact name"
        )
        digest = checked_sha256(item["sha256"], "validation artifact")
        backend, case_id, scope = validation_artifact_scope(
            kind, name, checked_components, selected_cases
        )
        expected_artifact = f"evidence/artifacts/{digest}"
        if item["artifact"] != expected_artifact:
            raise ValidationError(
                "validation artifact has noncanonical artifact path"
            )
        content = verify_evidence_file(
            report_root,
            item["artifact"],
            digest,
            f"validation artifact {kind}:{name}",
        )
        artifacts.append(ValidationArtifact(kind, name, digest, content))
        if kind == "backend-result":
            if case_id is None or backend not in checked_backends:
                raise ValidationError("backend-result artifact has no case")
            try:
                record = json.loads(content.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValidationError(
                    "backend-result artifact is not JSON"
                ) from error
            if not isinstance(record, dict):
                raise ValidationError("backend-result artifact is malformed")
            recorded_case_id, _ = checked_record(record, backend)
            if recorded_case_id != case_id:
                raise ValidationError(
                    "backend-result artifact disagrees with its name"
                )
            result_records[(case_id, backend)] = record
        elif kind == "build-determinism":
            if backend in determinism_backends:
                raise ValidationError(
                    "validation matrix has duplicate build determinism reports"
                )
            determinism_backends.add(backend)
            try:
                report = json.loads(content.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValidationError(
                    "build-determinism artifact is not JSON"
                ) from error
            if (
                not isinstance(report, dict)
                or set(report) != {"version", "backend", "equal", "attempts"}
                or report["version"] != PROTOCOL_VERSION
                or isinstance(report["version"], bool)
                or report["backend"] != backend
                or not isinstance(report["equal"], bool)
                or not isinstance(report["attempts"], list)
                or len(report["attempts"]) < 2
            ):
                raise ValidationError(
                    "build-determinism artifact is malformed"
                )
            checked_attempts: list[
                tuple[list[dict[str, str]], list[dict[str, str]]]
            ] = []
            for expected_attempt, attempt in enumerate(
                report["attempts"], start=1
            ):
                if (
                    not isinstance(attempt, dict)
                    or set(attempt)
                    != {"attempt", "products", "buildInputs"}
                    or attempt["attempt"] != expected_attempt
                    or isinstance(attempt["attempt"], bool)
                    or not isinstance(attempt["products"], list)
                    or not isinstance(attempt["buildInputs"], list)
                ):
                    raise ValidationError(
                        "build-determinism attempt is malformed"
                    )
                for inventory_name in ("products", "buildInputs"):
                    inventory = attempt[inventory_name]
                    for entry in inventory:
                        if (
                            not isinstance(entry, dict)
                            or set(entry)
                            != {"backend", "kind", "name", "sha256"}
                            or entry["backend"] != backend
                        ):
                            raise ValidationError(
                                f"build-determinism {inventory_name} "
                                "inventory is malformed"
                            )
                        validate_backend_name(
                            entry["kind"],
                            f"build-determinism {inventory_name} kind",
                        )
                        checked_relative_posix_path(
                            entry["name"],
                            f"build-determinism {inventory_name} name",
                        )
                        checked_sha256(
                            entry["sha256"],
                            f"build-determinism {inventory_name}",
                        )
                    keys = [
                        (entry["kind"], entry["name"])
                        for entry in inventory
                    ]
                    if len(set(keys)) != len(keys) or keys != sorted(keys):
                        raise ValidationError(
                            f"build-determinism {inventory_name} "
                            "inventory is malformed"
                        )
                checked_attempts.append(
                    (attempt["products"], attempt["buildInputs"])
                )
            actual_equal = all(
                attempt == checked_attempts[0]
                for attempt in checked_attempts[1:]
            )
            if report["equal"] != actual_equal:
                raise ValidationError(
                    "build-determinism equality disagrees with attempts"
                )
            determinism_attempt_counts[backend] = len(checked_attempts)
            determinism_attempts[backend] = checked_attempts
            final_products = [
                product.to_json()
                for product in products
                if product.backend == backend
            ]
            final_build_inputs = [
                build_input.to_json()
                for build_input in build_inputs
                if build_input.backend == backend
            ]
            if checked_attempts[-1] != (
                final_products,
                final_build_inputs,
            ):
                raise ValidationError(
                    "build-determinism final attempt disagrees with matrix"
                )
        elif kind == "build-file-access":
            if backend in file_access_reports:
                raise ValidationError(
                    "validation matrix has duplicate build file-access reports"
                )
            try:
                report = json.loads(content.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValidationError(
                    "build-file-access artifact is not JSON"
                ) from error
            if not isinstance(report, dict):
                raise ValidationError(
                    "build-file-access artifact is malformed"
                )
            file_access_reports[backend] = report
        elif kind == "build-file-access-trace":
            trace_key = (backend, scope)
            if trace_key in file_access_traces:
                raise ValidationError(
                    "validation matrix has duplicate build file-access traces"
                )
            file_access_traces[trace_key] = ValidationArtifact(
                kind, name, digest, content
            )
        elif kind == "execution-file-access":
            if backend in execution_access_reports:
                raise ValidationError(
                    "validation matrix has duplicate execution file-access reports"
                )
            try:
                report = json.loads(content.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValidationError(
                    "execution-file-access artifact is not JSON"
                ) from error
            if not isinstance(report, dict):
                raise ValidationError(
                    "execution-file-access artifact is malformed"
                )
            execution_access_reports[backend] = report
        elif kind == "execution-file-access-trace":
            if backend in execution_access_traces:
                raise ValidationError(
                    "validation matrix has duplicate execution file-access traces"
                )
            execution_access_traces[backend] = ValidationArtifact(
                kind, name, digest, content
            )
        elif kind == "execution-input":
            if backend in execution_inputs:
                raise ValidationError(
                    "validation matrix has duplicate execution inputs"
                )
            consumer = consumer_by_backend.get(backend)
            bundle = (
                bundle_by_provider.get(consumer.provider)
                if consumer is not None
                else None
            )
            exposed_products = (
                bundle.products
                if bundle is not None
                else tuple(
                    product
                    for product in products
                    if product.backend == backend
                )
            )
            execution_inputs[backend] = checked_execution_input(
                content,
                backend,
                selected_cases,
                exposed_products,
                bundle,
                f"retained {backend} execution input",
            )
        elif kind == "build-input-replay":
            if backend in replay_reports:
                raise ValidationError(
                    "validation matrix has duplicate build-input replay reports"
                )
            try:
                report = json.loads(content.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValidationError(
                    "build-input-replay artifact is not JSON"
                ) from error
            if not isinstance(report, dict):
                raise ValidationError(
                    "build-input-replay artifact is malformed"
                )
            replay_reports[backend] = report
        elif kind == "build-input-replay-trace":
            if backend in replay_traces:
                raise ValidationError(
                    "validation matrix has duplicate build-input replay traces"
                )
            replay_traces[backend] = ValidationArtifact(
                kind, name, digest, content
            )
        elif kind == "build-input-replay-status":
            if backend in replay_statuses:
                raise ValidationError(
                    "validation matrix has duplicate build-input replay statuses"
                )
            replay_statuses[backend] = ValidationArtifact(
                kind, name, digest, content
            )
        elif kind == "build-input-replay-manifest":
            if backend in replay_manifests:
                raise ValidationError(
                    "validation matrix has duplicate build-input replay manifests"
                )
            replay_manifests[backend] = ValidationArtifact(
                kind, name, digest, content
            )
        elif kind == "process-stdout":
            stdout_scopes.add((backend, case_id, scope))
        elif kind == "process-stderr":
            stderr_scopes.add((backend, case_id, scope))
        else:
            raise ValidationError("validation artifact kind is malformed")
    artifact_keys = [(artifact.kind, artifact.name) for artifact in artifacts]
    if len(set(artifact_keys)) != len(artifact_keys):
        raise ValidationError("validation matrix has duplicate artifacts")
    if artifact_keys != sorted(artifact_keys):
        raise ValidationError("validation matrix artifacts are not sorted")
    if stdout_scopes != stderr_scopes:
        raise ValidationError("validation process artifacts are not paired")
    repeat_log_backends = {
        backend
        for backend, case_id, scope in stdout_scopes
        if case_id is None
        and is_build_attempt_scope(scope)
        and scope != "build"
    }
    if repeat_log_backends != determinism_backends:
        raise ValidationError(
            "repeat-build process artifacts disagree with determinism reports"
        )
    for backend, attempt_count in determinism_attempt_counts.items():
        expected_scopes = {
            (
                backend,
                None,
                "build" if attempt == 1 else f"build-{attempt}",
            )
            for attempt in range(1, attempt_count + 1)
        }
        actual_scopes = {
            scope
            for scope in stdout_scopes
            if scope[0] == backend
            and scope[1] is None
            and is_build_attempt_scope(scope[2])
        }
        if actual_scopes != expected_scopes:
            raise ValidationError(
                "build-determinism attempts disagree with process artifacts"
            )

    expected_file_access_traces: set[tuple[str, str]] = set()
    tool_records = [tool.to_json() for tool in tools]
    recorder_tool_backends: list[str] = [
        tool.backend
        for tool in tools
        if tool.kind == BUILD_FILE_ACCESS_RECORDER_KIND
    ]
    if (
        len(set(recorder_tool_backends)) != len(recorder_tool_backends)
        or set(recorder_tool_backends) != set(file_access_reports)
    ):
        raise ValidationError(
            "build file-access recorder tools disagree with reports"
        )
    for backend, report in file_access_reports.items():
        if (
            set(report)
            != {
                "version",
                "backend",
                "recorder",
                "accessSetsEqual",
                "reportedInputsEqual",
                "attempts",
            }
            or report.get("version") != PROTOCOL_VERSION
            or isinstance(report.get("version"), bool)
            or report.get("backend") != backend
            or not isinstance(report.get("recorder"), dict)
            or not isinstance(report.get("accessSetsEqual"), bool)
            or not isinstance(report.get("reportedInputsEqual"), bool)
            or not isinstance(report.get("attempts"), list)
            or not report["attempts"]
        ):
            raise ValidationError(
                "build-file-access artifact is malformed"
            )
        recorder = report["recorder"]
        if (
            set(recorder) != {"backend", "kind", "name", "sha256"}
            or recorder.get("backend") != backend
        ):
            raise ValidationError(
                "build-file-access recorder is malformed"
            )
        validate_backend_name(
            recorder.get("kind"), "build-file-access recorder kind"
        )
        if recorder.get("kind") != BUILD_FILE_ACCESS_RECORDER_KIND:
            raise ValidationError(
                "build-file-access recorder kind is malformed"
            )
        checked_relative_posix_path(
            recorder.get("name"), "build-file-access recorder name"
        )
        checked_sha256(
            recorder.get("sha256"), "build-file-access recorder"
        )
        if recorder not in tool_records:
            raise ValidationError(
                "build-file-access recorder is absent from validation tools"
            )
        expected_attempt_count = determinism_attempt_counts.get(backend, 1)
        if len(report["attempts"]) != expected_attempt_count:
            raise ValidationError(
                "build-file-access attempts disagree with build determinism"
            )
        for expected_attempt, attempt in enumerate(
            report["attempts"], start=1
        ):
            if (
                not isinstance(attempt, dict)
                or set(attempt)
                != {
                    "attempt",
                    "trace",
                    "accesses",
                    "accessCount",
                    "reportedInputs",
                    "reportedInputCount",
                }
                or attempt.get("attempt") != expected_attempt
                or isinstance(attempt.get("attempt"), bool)
                or not isinstance(attempt.get("trace"), dict)
                or not isinstance(attempt.get("accesses"), list)
                or not isinstance(attempt.get("accessCount"), int)
                or isinstance(attempt.get("accessCount"), bool)
                or not isinstance(attempt.get("reportedInputs"), list)
                or not isinstance(attempt.get("reportedInputCount"), int)
                or isinstance(attempt.get("reportedInputCount"), bool)
            ):
                raise ValidationError(
                    "build-file-access attempt is malformed"
                )
            scope = (
                "build"
                if expected_attempt == 1
                else f"build-{expected_attempt}"
            )
            expected_trace_name = (
                f"{backend}/{scope}/file-access.strace"
            )
            trace = attempt["trace"]
            if (
                set(trace) != {"name", "sha256"}
                or trace.get("name") != expected_trace_name
            ):
                raise ValidationError(
                    "build-file-access trace reference is malformed"
                )
            trace_digest = checked_sha256(
                trace.get("sha256"), "build-file-access trace"
            )
            trace_key = (backend, scope)
            expected_file_access_traces.add(trace_key)
            trace_artifact = file_access_traces.get(trace_key)
            if (
                trace_artifact is None
                or trace_artifact.name != expected_trace_name
                or trace_artifact.sha256 != trace_digest
            ):
                raise ValidationError(
                    "build-file-access report disagrees with raw trace"
                )
            parsed_accesses = parse_build_file_access_trace(
                trace_artifact.content,
                f"retained {backend} build file-access trace "
                f"attempt {expected_attempt}",
            )
            canonical_accesses = [
                {"path": path, "accesses": list(kinds)}
                for path, kinds in parsed_accesses.items()
            ]
            if attempt["accesses"] != canonical_accesses:
                raise ValidationError(
                    "build-file-access report disagrees with parsed trace"
                )
            if attempt["accessCount"] != len(canonical_accesses):
                raise ValidationError(
                    "build-file-access access count is malformed"
                )
            reported_records: list[dict[str, str]] = []
            reported_keys: list[tuple[str, str]] = []
            for item in attempt["reportedInputs"]:
                if (
                    not isinstance(item, dict)
                    or set(item)
                    != {
                        "backend",
                        "kind",
                        "name",
                        "sha256",
                        "path",
                        "accesses",
                    }
                    or item.get("backend") != backend
                ):
                    raise ValidationError(
                        "build-file-access reported input is malformed"
                    )
                kind = validate_backend_name(
                    item.get("kind"),
                    "build-file-access reported input kind",
                )
                name = checked_relative_posix_path(
                    item.get("name"),
                    "build-file-access reported input name",
                )
                digest = checked_sha256(
                    item.get("sha256"),
                    "build-file-access reported input",
                )
                input_path = item.get("path")
                if (
                    not isinstance(input_path, str)
                    or not os.path.isabs(input_path)
                    or os.path.normpath(input_path) != input_path
                    or item.get("accesses")
                    != list(parsed_accesses.get(input_path, ()))
                    or not item.get("accesses")
                ):
                    raise ValidationError(
                        "build-file-access reported input was not observed"
                    )
                reported_records.append(
                    {
                        "backend": backend,
                        "kind": kind,
                        "name": name,
                        "sha256": digest,
                    }
                )
                reported_keys.append((kind, name))
            if (
                len(set(reported_keys)) != len(reported_keys)
                or reported_keys != sorted(reported_keys)
            ):
                raise ValidationError(
                    "build-file-access reported inputs are duplicate or unsorted"
                )
            if attempt["reportedInputCount"] != len(reported_records):
                raise ValidationError(
                    "build-file-access reported input count is malformed"
                )
            if backend in determinism_attempts:
                expected_inputs = determinism_attempts[backend][
                    expected_attempt - 1
                ][1]
            else:
                expected_inputs = [
                    item.to_json()
                    for item in build_inputs
                    if item.backend == backend
                ]
            expected_reported_inputs = [
                item
                for item in expected_inputs
                if item["kind"] != RESERVED_BUILD_INPUT_KIND
            ]
            if reported_records != expected_reported_inputs:
                raise ValidationError(
                    "build-file-access reported inputs disagree with build inputs"
                )
        actual_access_sets_equal = all(
            attempt["accesses"] == report["attempts"][0]["accesses"]
            for attempt in report["attempts"][1:]
        )
        actual_reported_inputs_equal = all(
            attempt["reportedInputs"]
            == report["attempts"][0]["reportedInputs"]
            for attempt in report["attempts"][1:]
        )
        if (
            report["accessSetsEqual"] != actual_access_sets_equal
            or report["reportedInputsEqual"]
            != actual_reported_inputs_equal
        ):
            raise ValidationError(
                "build-file-access equality disagrees with attempts"
            )
        expected_scopes = {
            (
                backend,
                None,
                "build" if attempt == 1 else f"build-{attempt}",
            )
            for attempt in range(1, expected_attempt_count + 1)
        }
        actual_scopes = {
            item
            for item in stdout_scopes
            if item[0] == backend
            and item[1] is None
            and is_build_attempt_scope(item[2])
        }
        if actual_scopes != expected_scopes:
            raise ValidationError(
                "build-file-access attempts disagree with process artifacts"
            )
    if set(file_access_traces) != expected_file_access_traces:
        raise ValidationError(
            "raw build file-access traces disagree with reports"
        )

    replay_tool_backends = [
        tool.backend
        for tool in tools
        if tool.kind == BUILD_INPUT_REPLAY_ISOLATOR_KIND
    ]
    replay_backends = set(replay_reports)
    if (
        len(set(replay_tool_backends)) != len(replay_tool_backends)
        or set(replay_tool_backends) != replay_backends
        or set(replay_traces) != replay_backends
        or set(replay_statuses) != replay_backends
        or set(replay_manifests) != replay_backends
    ):
        raise ValidationError(
            "build-input replay tools and artifacts disagree"
        )
    expected_replay_policy = {
        "mode": "content-addressed-declared-closure",
        "ambientRoot": "read-only",
        "network": "unshared",
        "nestedUserNamespaces": "disabled",
        "reportedInputs": "content-addressed-read-only-overlays",
        "temporaryDirectory": "fresh",
        "output": "isolated-writable",
    }
    for backend, report in replay_reports.items():
        expected_fields = {
            "version",
            "backend",
            "isolator",
            "recorder",
            "policy",
            "sourceAttempt",
            "command",
            "cwd",
            "environment",
            "writableRoot",
            "bindings",
            "trace",
            "accesses",
            "accessCount",
            "reportedInputs",
            "reportedInputCount",
            "ambientAccessCount",
            "sandboxStatus",
            "buildInputManifest",
            "products",
            "buildInputs",
            "productsEqual",
            "buildInputsEqual",
            "equal",
        }
        if (
            set(report) != expected_fields
            or report.get("version") != PROTOCOL_VERSION
            or isinstance(report.get("version"), bool)
            or report.get("backend") != backend
            or report.get("policy") != expected_replay_policy
            or not isinstance(report.get("isolator"), dict)
            or not isinstance(report.get("recorder"), dict)
            or not isinstance(report.get("command"), list)
            or not report["command"]
            or not all(
                isinstance(argument, str) and argument
                for argument in report["command"]
            )
            or not isinstance(report.get("environment"), dict)
            or not isinstance(report.get("bindings"), list)
            or not report["bindings"]
            or not isinstance(report.get("accesses"), list)
            or not isinstance(report.get("reportedInputs"), list)
            or not isinstance(report.get("products"), list)
            or not isinstance(report.get("buildInputs"), list)
            or not isinstance(report.get("productsEqual"), bool)
            or not isinstance(report.get("buildInputsEqual"), bool)
            or not isinstance(report.get("equal"), bool)
        ):
            raise ValidationError(
                "build-input-replay artifact is malformed"
            )
        expected_source_attempt = determinism_attempt_counts.get(backend, 1)
        if (
            report.get("sourceAttempt") != expected_source_attempt
            or isinstance(report.get("sourceAttempt"), bool)
        ):
            raise ValidationError(
                "build-input replay names the wrong source attempt"
            )
        isolator = report["isolator"]
        recorder = report["recorder"]
        for role, record, expected_kind in (
            (
                "isolator",
                isolator,
                BUILD_INPUT_REPLAY_ISOLATOR_KIND,
            ),
            ("recorder", recorder, BUILD_FILE_ACCESS_RECORDER_KIND),
        ):
            if (
                set(record) != {"backend", "kind", "name", "sha256"}
                or record.get("backend") != backend
                or record.get("kind") != expected_kind
            ):
                raise ValidationError(
                    f"build-input replay {role} is malformed"
                )
            checked_relative_posix_path(
                record.get("name"), f"build-input replay {role} name"
            )
            checked_sha256(
                record.get("sha256"), f"build-input replay {role}"
            )
            if record not in tool_records:
                raise ValidationError(
                    f"build-input replay {role} is absent from tools"
                )

        trace_reference = report["trace"]
        expected_trace_name = (
            f"{backend}/build-input-replay/file-access.strace"
        )
        trace_artifact = replay_traces[backend]
        if (
            not isinstance(trace_reference, dict)
            or set(trace_reference) != {"name", "sha256"}
            or trace_reference.get("name") != expected_trace_name
            or trace_artifact.name != expected_trace_name
            or trace_artifact.sha256
            != checked_sha256(
                trace_reference.get("sha256"),
                "build-input replay trace",
            )
        ):
            raise ValidationError(
                "build-input replay disagrees with its trace"
            )
        replay_accesses = parse_build_file_access_trace(
            trace_artifact.content,
            f"retained {backend} build-input replay trace",
        )
        canonical_replay_accesses = [
            {"path": path, "accesses": list(kinds)}
            for path, kinds in replay_accesses.items()
        ]
        if (
            report["accesses"] != canonical_replay_accesses
            or report.get("accessCount") != len(replay_accesses)
            or isinstance(report.get("accessCount"), bool)
        ):
            raise ValidationError(
                "build-input replay access report is malformed"
            )

        status_reference = report["sandboxStatus"]
        expected_status_name = (
            f"{backend}/build-input-replay/sandbox-status.jsonl"
        )
        status_artifact = replay_statuses[backend]
        if (
            not isinstance(status_reference, dict)
            or set(status_reference) != {"name", "sha256"}
            or status_reference.get("name") != expected_status_name
            or status_artifact.name != expected_status_name
            or status_artifact.sha256
            != checked_sha256(
                status_reference.get("sha256"),
                "build-input replay sandbox status",
            )
        ):
            raise ValidationError(
                "build-input replay disagrees with sandbox status"
            )
        parse_bwrap_status(
            status_artifact.content,
            f"retained {backend} build-input replay status",
        )

        manifest_reference = report["buildInputManifest"]
        expected_manifest_name = (
            f"{backend}/build-input-replay/build-input-manifest.json"
        )
        manifest_artifact = replay_manifests[backend]
        if (
            not isinstance(manifest_reference, dict)
            or set(manifest_reference) != {"name", "sha256"}
            or manifest_reference.get("name") != expected_manifest_name
            or manifest_artifact.name != expected_manifest_name
            or manifest_artifact.sha256
            != checked_sha256(
                manifest_reference.get("sha256"),
                "build-input replay manifest",
            )
        ):
            raise ValidationError(
                "build-input replay disagrees with its input manifest"
            )
        replay_declarations = build_input_declarations_from_manifest(
            manifest_artifact.content,
            f"retained {backend} build-input replay manifest",
        )

        environment = report["environment"]
        required_environment_fields = {
            "HOME",
            "LANG",
            "LC_ALL",
            "PATH",
            "TERM",
            "TMPDIR",
            "FIR_VALIDATION_BACKEND",
            "FIR_VALIDATION_OUT_DIR",
            "FIR_VALIDATION_PROTOCOL_VERSION",
            "FIR_VALIDATION_CASES",
            "FIR_VALIDATION_CORPUS",
            "FIR_VALIDATION_BUILD_TOOLS",
        }
        writable_root = report.get("writableRoot")
        cwd = report.get("cwd")
        if (
            set(environment) != required_environment_fields
            or not all(
                isinstance(key, str) and isinstance(value, str)
                for key, value in environment.items()
            )
            or environment.get("HOME") != "/tmp/home"
            or environment.get("LANG") != "C.UTF-8"
            or environment.get("LC_ALL") != "C.UTF-8"
            or environment.get("TERM") != "dumb"
            or environment.get("TMPDIR") != "/tmp"
            or environment.get("FIR_VALIDATION_BACKEND") != backend
            or environment.get("FIR_VALIDATION_PROTOCOL_VERSION")
            != str(PROTOCOL_VERSION)
            or environment.get("FIR_VALIDATION_CASES")
            != json.dumps(selected_cases, separators=(",", ":"))
            or not isinstance(writable_root, str)
            or not os.path.isabs(writable_root)
            or os.path.normpath(writable_root) != writable_root
            or environment.get("FIR_VALIDATION_OUT_DIR") != writable_root
            or not isinstance(cwd, str)
            or not os.path.isabs(cwd)
            or os.path.normpath(cwd) != cwd
        ):
            raise ValidationError(
                "build-input replay environment is malformed"
            )
        try:
            environment_tools = json.loads(
                environment["FIR_VALIDATION_BUILD_TOOLS"]
            )
        except json.JSONDecodeError as error:
            raise ValidationError(
                "build-input replay tool environment is malformed"
            ) from error
        if not isinstance(environment_tools, list):
            raise ValidationError(
                "build-input replay tool environment is malformed"
            )
        checked_environment_tools: list[dict[str, str]] = []
        for item in environment_tools:
            if (
                not isinstance(item, dict)
                or set(item)
                != {"backend", "kind", "name", "sha256", "path"}
                or item.get("backend") != backend
                or not isinstance(item.get("path"), str)
                or not os.path.isabs(item["path"])
                or os.path.normpath(item["path"]) != item["path"]
            ):
                raise ValidationError(
                    "build-input replay tool environment is malformed"
                )
            logical = {
                field: item[field]
                for field in ("backend", "kind", "name", "sha256")
            }
            validate_backend_name(
                logical["kind"], "build-input replay tool kind"
            )
            checked_relative_posix_path(
                logical["name"], "build-input replay tool name"
            )
            checked_sha256(
                logical["sha256"], "build-input replay tool"
            )
            if logical not in tool_records:
                raise ValidationError(
                    "build-input replay environment names an unknown tool"
                )
            checked_environment_tools.append(item)
        environment_tool_keys = [
            (item["kind"], item["name"])
            for item in checked_environment_tools
        ]
        if (
            len(set(environment_tool_keys)) != len(environment_tool_keys)
            or environment_tool_keys != sorted(environment_tool_keys)
            or isolator not in [
                {
                    field: item[field]
                    for field in ("backend", "kind", "name", "sha256")
                }
                for item in checked_environment_tools
            ]
            or recorder not in [
                {
                    field: item[field]
                    for field in ("backend", "kind", "name", "sha256")
                }
                for item in checked_environment_tools
            ]
        ):
            raise ValidationError(
                "build-input replay tool environment is malformed"
            )

        matching_configs: list[
            tuple[str, str, dict[str, object]]
        ] = []
        for (input_kind, input_name), input_content in input_contents.items():
            if input_kind not in {"adapter-config", "provider-config"}:
                continue
            try:
                config_value = json.loads(input_content.decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ValidationError(
                    "retained validation adapter config is not JSON"
                ) from error
            if (
                isinstance(config_value, dict)
                and config_value.get("name") == backend
            ):
                matching_configs.append(
                    (input_kind, input_name, config_value)
                )
        if len(matching_configs) != 1:
            raise ValidationError(
                "build-input replay has no unique retained producer config"
            )
        _, config_name, producer_config = matching_configs[0]
        raw_replay_command = producer_config.get("buildReplayCommand")
        raw_build_tools = producer_config.get("buildTools")
        if (
            not isinstance(raw_replay_command, list)
            or not raw_replay_command
            or not all(
                isinstance(argument, str) and argument
                for argument in raw_replay_command
            )
            or not isinstance(raw_build_tools, list)
            or not raw_build_tools
        ):
            raise ValidationError(
                "retained build-input replay declaration is malformed"
            )
        ordinary_environment_tools = {
            (item["kind"], item["name"]): item
            for item in checked_environment_tools
            if item["kind"]
            not in {
                BUILD_FILE_ACCESS_RECORDER_KIND,
                BUILD_INPUT_REPLAY_ISOLATOR_KIND,
            }
        }
        declared_tool_keys: set[tuple[str, str]] = set()
        bound_replay_command = list(raw_replay_command)
        command_tool_count = 0
        config_path = Path(cwd) / config_name
        for item in raw_build_tools:
            if (
                not isinstance(item, dict)
                or not isinstance(item.get("kind"), str)
                or not isinstance(item.get("name"), str)
            ):
                raise ValidationError(
                    "retained build-input replay tools are malformed"
                )
            key = (item["kind"], item["name"])
            tool = ordinary_environment_tools.get(key)
            if key in declared_tool_keys or tool is None:
                raise ValidationError(
                    "retained build-input replay tools disagree with evidence"
                )
            declared_tool_keys.add(key)
            if "command" in item:
                command_tool_count += 1
                if (
                    item.get("command") != bound_replay_command[0]
                    or "path" in item
                ):
                    raise ValidationError(
                        "retained build-input replay command tool is malformed"
                    )
                bound_replay_command[0] = tool["path"]
                continue
            raw_path = item.get("path")
            if not isinstance(raw_path, str) or "command" in item:
                raise ValidationError(
                    "retained build-input replay path tool is malformed"
                )
            declaration_path = Path(
                os.path.abspath(config_path.parent / raw_path)
            )
            matches = [
                index
                for index, argument in enumerate(
                    bound_replay_command[1:], start=1
                )
                if Path(
                    os.path.abspath(
                        Path(argument)
                        if Path(argument).is_absolute()
                        else Path(cwd) / argument
                    )
                )
                == declaration_path
            ]
            if len(matches) != 1:
                raise ValidationError(
                    "retained build-input replay path tool is unbound"
                )
            bound_replay_command[matches[0]] = tool["path"]
        if (
            command_tool_count != 1
            or declared_tool_keys != set(ordinary_environment_tools)
            or report["command"] != bound_replay_command
        ):
            raise ValidationError(
                "build-input replay command disagrees with retained config"
            )

        source_attempt = file_access_reports[backend]["attempts"][
            expected_source_attempt - 1
        ]
        source_accesses = {
            item["path"]: item["accesses"]
            for item in source_attempt["accesses"]
        }
        source_reported_inputs = source_attempt["reportedInputs"]
        expected_bindings: list[dict[str, object]] = []
        for item in source_reported_inputs:
            accesses = item["accesses"]
            expected_bindings.append(
                {
                    "backend": backend,
                    "category": "build-input",
                    "kind": item["kind"],
                    "name": item["name"],
                    "sha256": item["sha256"],
                    "path": item["path"],
                    "mode": 0o555 if "exec" in accesses else 0o444,
                    "accesses": accesses,
                    "blob": f"evidence/build-inputs/{item['sha256']}",
                }
            )
        for item in checked_environment_tools:
            if item["kind"] in {
                BUILD_FILE_ACCESS_RECORDER_KIND,
                BUILD_INPUT_REPLAY_ISOLATOR_KIND,
            }:
                continue
            accesses = source_accesses.get(item["path"], [])
            if not accesses:
                raise ValidationError(
                    "build-input replay tool was absent from source trace"
                )
            expected_bindings.append(
                {
                    "backend": backend,
                    "category": "build-tool",
                    "kind": item["kind"],
                    "name": item["name"],
                    "sha256": item["sha256"],
                    "path": item["path"],
                    "mode": 0o555 if "exec" in accesses else 0o444,
                    "accesses": accesses,
                    "blob": f"evidence/tools/{item['sha256']}",
                }
            )
        corpus_input = inputs[0]
        corpus_path = environment.get("FIR_VALIDATION_CORPUS")
        if (
            corpus_input.kind != "corpus"
            or corpus_input.name != "corpus.json"
            or not isinstance(corpus_path, str)
            or not os.path.isabs(corpus_path)
            or os.path.normpath(corpus_path) != corpus_path
        ):
            raise ValidationError(
                "build-input replay corpus binding is malformed"
            )
        corpus_accesses = source_accesses.get(corpus_path, [])
        expected_bindings.append(
            {
                "backend": backend,
                "category": "validation-input",
                "kind": corpus_input.kind,
                "name": corpus_input.name,
                "sha256": corpus_input.sha256,
                "path": corpus_path,
                "mode": 0o555 if "exec" in corpus_accesses else 0o444,
                "accesses": corpus_accesses,
                "blob": f"evidence/inputs/{corpus_input.sha256}",
            }
        )
        expected_bindings.sort(
            key=lambda item: (
                str(item["category"]),
                str(item["kind"]),
                str(item["name"]),
            )
        )
        if report["bindings"] != expected_bindings:
            raise ValidationError(
                "build-input replay bindings disagree with source evidence"
            )
        binding_paths = [str(item["path"]) for item in expected_bindings]
        if (
            len(set(binding_paths)) != len(binding_paths)
            or any(
                path == writable_root or path.startswith(f"{writable_root}/")
                for path in binding_paths
            )
        ):
            raise ValidationError(
                "build-input replay bindings collide"
            )
        executable_directories = sorted(
            {
                str(Path(str(item["path"])).parent)
                for item in expected_bindings
                if item["category"] == "build-input"
                and "exec" in item["accesses"]
            }
        )
        expected_path = ":".join(
            dict.fromkeys((*executable_directories, "/usr/bin", "/bin"))
        )
        if environment.get("PATH") != expected_path:
            raise ValidationError(
                "build-input replay PATH is malformed"
            )
        command_tool_bindings = [
            item
            for item in expected_bindings
            if item["category"] == "build-tool"
        ]
        exec_tools = [
            item for item in command_tool_bindings
            if "exec" in item["accesses"]
        ]
        if (
            len(exec_tools) != 1
            or report["command"][0] != exec_tools[0]["path"]
            or any(
                report["command"].count(str(item["path"])) != 1
                for item in command_tool_bindings
            )
        ):
            raise ValidationError(
                "build-input replay command disagrees with build tools"
            )
        for item in expected_bindings:
            expected_accesses = tuple(item["accesses"])
            if item["category"] == "validation-input":
                continue
            if replay_accesses.get(str(item["path"])) != expected_accesses:
                raise ValidationError(
                    "build-input replay did not preserve declared accesses"
                )
        if (
            report.get("ambientAccessCount")
            != len(set(replay_accesses) - set(binding_paths))
            or isinstance(report.get("ambientAccessCount"), bool)
        ):
            raise ValidationError(
                "build-input replay ambient access count is malformed"
            )

        def checked_replay_inventory(
            inventory: object, label: str
        ) -> list[dict[str, str]]:
            if not isinstance(inventory, list):
                raise ValidationError(
                    f"build-input replay {label} is malformed"
                )
            checked: list[dict[str, str]] = []
            for item in inventory:
                if (
                    not isinstance(item, dict)
                    or set(item)
                    != {"backend", "kind", "name", "sha256"}
                    or item.get("backend") != backend
                ):
                    raise ValidationError(
                        f"build-input replay {label} is malformed"
                    )
                validate_backend_name(
                    item.get("kind"), f"build-input replay {label} kind"
                )
                checked_relative_posix_path(
                    item.get("name"), f"build-input replay {label} name"
                )
                checked_sha256(
                    item.get("sha256"), f"build-input replay {label}"
                )
                checked.append(item)
            keys = [(item["kind"], item["name"]) for item in checked]
            if len(set(keys)) != len(keys) or keys != sorted(keys):
                raise ValidationError(
                    f"build-input replay {label} is duplicate or unsorted"
                )
            return checked

        replay_products = checked_replay_inventory(
            report["products"], "products"
        )
        replay_build_inputs = checked_replay_inventory(
            report["buildInputs"], "build inputs"
        )
        replay_reported_records: list[dict[str, str]] = []
        replay_reported_paths: list[tuple[str, str, str]] = []
        replay_reported_bindings: list[tuple[str, str, str, str]] = []
        for item in report["reportedInputs"]:
            if (
                not isinstance(item, dict)
                or set(item)
                != {
                    "backend",
                    "kind",
                    "name",
                    "sha256",
                    "path",
                    "accesses",
                }
                or item.get("backend") != backend
            ):
                raise ValidationError(
                    "build-input replay reported input is malformed"
                )
            logical = {
                field: item[field]
                for field in ("backend", "kind", "name", "sha256")
            }
            validate_backend_name(
                logical["kind"], "build-input replay input kind"
            )
            checked_relative_posix_path(
                logical["name"], "build-input replay input name"
            )
            checked_sha256(
                logical["sha256"], "build-input replay input"
            )
            input_path = item.get("path")
            if (
                not isinstance(input_path, str)
                or not os.path.isabs(input_path)
                or os.path.normpath(input_path) != input_path
                or item.get("accesses")
                != list(replay_accesses.get(input_path, ()))
                or not item.get("accesses")
            ):
                raise ValidationError(
                    "build-input replay reported input was not observed"
                )
            replay_reported_records.append(logical)
            replay_reported_paths.append(
                (logical["kind"], logical["name"], input_path)
            )
            replay_reported_bindings.append(
                (
                    logical["kind"],
                    logical["name"],
                    logical["sha256"],
                    input_path,
                )
            )
        expected_reported_bindings = [
            (
                str(item["kind"]),
                str(item["name"]),
                str(item["sha256"]),
                str(item["path"]),
            )
            for item in expected_bindings
            if item["category"] == "build-input"
        ]
        expected_reported_paths = {
            (kind, name): path
            for kind, name, _, path in expected_reported_bindings
        }
        replay_manifest_paths: list[tuple[str, str, str]] = []
        for item in replay_declarations:
            key = (item.kind, item.name)
            raw_path = os.path.normpath(str(item.path))
            expected_path = expected_reported_paths.get(key)
            if (
                expected_path is not None
                and raw_path == f"{expected_path} (deleted)"
            ):
                raw_path = expected_path
            replay_manifest_paths.append((item.kind, item.name, raw_path))
        if (
            report.get("reportedInputCount")
            != len(replay_reported_records)
            or isinstance(report.get("reportedInputCount"), bool)
            or replay_reported_records
            != [
                item for item in replay_build_inputs
                if item["kind"] != RESERVED_BUILD_INPUT_KIND
            ]
            or replay_reported_paths != replay_manifest_paths
            or replay_reported_bindings != expected_reported_bindings
        ):
            raise ValidationError(
                "build-input replay manifest and reported inputs disagree"
            )
        replay_members = tuple(
            ValidationBuildInput(
                item["backend"],
                item["kind"],
                item["name"],
                item["sha256"],
            )
            for item in replay_reported_records
        )
        replay_manifest_records = [
            item for item in replay_build_inputs
            if item["kind"] == RESERVED_BUILD_INPUT_KIND
        ]
        if (
            len(replay_manifest_records) != 1
            or replay_manifest_records[0]["sha256"]
            != sha256_bytes(canonical_build_input_manifest_bytes(replay_members))
        ):
            raise ValidationError(
                "build-input replay canonical manifest is malformed"
            )
        final_products = [
            item.to_json() for item in products if item.backend == backend
        ]
        final_build_inputs = [
            item.to_json()
            for item in build_inputs if item.backend == backend
        ]
        products_equal = replay_products == final_products
        build_inputs_equal = replay_build_inputs == final_build_inputs
        if (
            report["productsEqual"] != products_equal
            or report["buildInputsEqual"] != build_inputs_equal
            or report["equal"] != (products_equal and build_inputs_equal)
        ):
            raise ValidationError(
                "build-input replay equality is malformed"
            )
        if (backend, None, "build-input-replay") not in stdout_scopes:
            raise ValidationError(
                "build-input replay has no paired process logs"
            )

    reconstructed_receipts: list[ProductReceipt] = []
    for consumer in product_consumers:
        bundle = bundle_by_provider[consumer.provider]
        for case_id in selected_cases:
            record = result_records.get((case_id, consumer.backend))
            if record is not None:
                reconstructed_receipts.append(
                    checked_product_bundle_receipt(
                        record, consumer.backend, case_id, bundle
                    )
                )
    reconstructed_receipts.sort(
        key=lambda receipt: (receipt.backend, receipt.case_id)
    )
    if reconstructed_receipts != product_receipts:
        raise ValidationError(
            "validation product receipts disagree with retained results"
        )

    raw_pairs = value["pairs"]
    if not isinstance(raw_pairs, list) or not raw_pairs:
        raise ValidationError("validation matrix has malformed pairs")
    pair_names: list[tuple[str, str]] = []
    coverage_pairs: list[tuple[str, str, int, int, int]] = []
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
        compared_case_ids: list[str] = []
        for compared in comparison["comparisons"]:
            if not isinstance(compared, dict) or set(compared) != {
                "caseId", "reference", "candidate", "equal", "case"
            }:
                raise ValidationError("validation comparison entry is malformed")
            case_id = validate_backend_name(
                compared["caseId"], "validation comparison case ID"
            )
            if (
                case_id not in selected_cases
                or compared["reference"] != reference
                or compared["candidate"] != candidate
                or not isinstance(compared["equal"], bool)
                or compared["case"] != corpus_cases[case_id]
            ):
                raise ValidationError(
                    "validation comparison entry disagrees with retained evidence"
                )
            reference_record = result_records.get((case_id, reference))
            candidate_record = result_records.get((case_id, candidate))
            if reference_record is None or candidate_record is None:
                raise ValidationError(
                    "validation comparison has no retained backend result"
                )
            try:
                equal, _, _ = compare_success(
                    reference_record, candidate_record
                )
            except ValidationError as error:
                raise ValidationError(
                    "validation comparison references a non-success result"
                ) from error
            if compared["equal"] != equal:
                raise ValidationError(
                    "validation comparison disagrees with retained backend results"
                )
            compared_case_ids.append(case_id)
        if (
            len(set(compared_case_ids)) != len(compared_case_ids)
            or compared_case_ids
            != [
                case_id
                for case_id in selected_cases
                if case_id in set(compared_case_ids)
            ]
            or sum(
                int(compared["equal"])
                for compared in comparison["comparisons"]
            )
            != equal_cases
        ):
            raise ValidationError("validation comparison entries are malformed")
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
        coverage_pairs.append(
            (
                reference,
                candidate,
                compared_cases,
                equal_cases,
                item["findingCount"],
            )
        )
        comparison_count += compared_cases
        equal_comparison_count += equal_cases
    if len(set(pair_names)) != len(pair_names):
        raise ValidationError("validation matrix has duplicate pairs")
    retained_adapters = validate_control_plane_inputs(
        inputs,
        checked_backends,
        pair_names,
        products,
        bundles,
        product_consumers,
        list(corpus_cases.values()),
        selected_cases,
    )
    expected_execution_input_backends = {
        backend
        for backend, case_id, scope in stdout_scopes
        if (
            case_id is None
            and scope == "execute"
            and backend in retained_adapters
        )
    }
    if not expected_execution_input_backends <= set(execution_inputs):
        raise ValidationError(
            "external execution process has no retained execution input"
        )
    verify_execution_file_access_evidence(
        execution_access_reports,
        execution_access_traces,
        retained_adapters,
        checked_backends,
        tools,
        bundles,
        product_consumers,
        product_receipts,
    )
    if any(
        (backend, None, "execute") not in stdout_scopes
        for backend in execution_access_reports
    ):
        raise ValidationError(
            "execution-file-access evidence has no paired process logs"
        )

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
    expected_coverage = validation_coverage_report(
        selected_cases,
        checked_backends,
        coverage_pairs,
        [finding.get("backend") for finding in findings],
        bundles,
        product_consumers,
        product_receipts,
        result_records,
        execution_access_reports,
    )
    if value["coverage"] != expected_coverage:
        raise ValidationError(
            "validation matrix coverage disagrees with retained evidence"
        )
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
        "toolCount",
        "buildInputCount",
        "artifactCount",
    }
    if has_providers:
        expected_summary_fields |= {
            "providerCount",
            "bundleCount",
            "productConsumerCount",
            "productReceiptCount",
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
        "toolCount": len(tools),
        "buildInputCount": len(build_inputs),
        "artifactCount": len(artifacts),
    }
    if has_providers:
        expected_summary.update(
            {
                "providerCount": len(checked_providers),
                "bundleCount": len(bundles),
                "productConsumerCount": len(product_consumers),
                "productReceiptCount": len(product_receipts),
            }
        )
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
        tools,
        build_inputs,
        bundles if has_providers else None,
        product_consumers if has_providers else None,
        product_receipts if has_providers else None,
    )
    if run_sha256 != expected_run_sha256:
        raise ValidationError("validation run identity mismatch")
    return value


def verify_evidence_snapshot(path: Path) -> VerifiedEvidence:
    """Verify and return one append-only manifest with its retained matrix."""
    absolute = Path(os.path.abspath(path))
    run_directory = absolute.parent
    runs_directory = run_directory.parent
    evidence_directory = runs_directory.parent
    report_root = evidence_directory.parent
    if (
        evidence_directory.name != "evidence"
        or runs_directory.name != "runs"
        or absolute.suffix != ".json"
    ):
        raise ValidationError(
            "validation evidence manifest has noncanonical path"
        )
    for component in (
        evidence_directory,
        runs_directory,
        run_directory,
        absolute,
    ):
        if component.is_symlink():
            raise ValidationError(
                "validation evidence manifest path contains a symlink"
            )
    if not absolute.is_file():
        raise ValidationError(
            f"validation evidence manifest is not a regular file: {path}"
        )
    try:
        manifest = json.loads(absolute.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"cannot read validation evidence manifest {path}: {error}"
        ) from error
    if not isinstance(manifest, dict) or set(manifest) != {
        "version", "identity", "matrix", "coverage"
    }:
        raise ValidationError("validation evidence manifest is malformed")
    if (
        not isinstance(manifest["version"], int)
        or isinstance(manifest["version"], bool)
        or manifest["version"] != PROTOCOL_VERSION
    ):
        raise ValidationError(
            "validation evidence manifest has unsupported version"
        )
    identity = manifest["identity"]
    if (
        not isinstance(identity, dict)
        or set(identity) != {"algorithm", "run", "evidence"}
        or identity["algorithm"] != "sha256"
    ):
        raise ValidationError(
            "validation evidence manifest has malformed identity"
        )
    run_sha256 = checked_sha256(identity["run"], "validation evidence run")
    evidence_sha256 = checked_sha256(
        identity["evidence"], "validation evidence identity"
    )
    matrix = manifest["matrix"]
    if not isinstance(matrix, dict) or set(matrix) != {"sha256", "artifact"}:
        raise ValidationError(
            "validation evidence manifest has malformed matrix"
        )
    matrix_sha256 = checked_sha256(
        matrix["sha256"], "validation evidence matrix"
    )
    if run_directory.name != run_sha256:
        raise ValidationError(
            "validation evidence manifest run directory mismatch"
        )
    if absolute.stem != evidence_sha256:
        raise ValidationError(
            "validation evidence manifest filename mismatch"
        )
    expected_evidence_sha256 = validation_evidence_sha256(
        run_sha256, matrix_sha256
    )
    if evidence_sha256 != expected_evidence_sha256:
        raise ValidationError("validation evidence identity mismatch")
    expected_artifact = f"evidence/matrices/{matrix_sha256}"
    if matrix["artifact"] != expected_artifact:
        raise ValidationError(
            "validation evidence manifest has noncanonical matrix artifact"
        )
    verify_evidence_file(
        report_root,
        matrix["artifact"],
        matrix_sha256,
        "retained validation matrix",
    )
    verified_matrix = verify_matrix_artifact(
        report_root / expected_artifact,
        report_root=report_root,
    )
    if verified_matrix["identity"]["run"] != run_sha256:
        raise ValidationError(
            "validation evidence run disagrees with retained matrix"
        )
    if manifest["coverage"] != verified_matrix["coverage"]:
        raise ValidationError(
            "validation evidence coverage disagrees with retained matrix"
        )
    return VerifiedEvidence(absolute, report_root, manifest, verified_matrix)


def verify_evidence_manifest(path: Path) -> dict:
    """Verify one append-only evidence manifest and its retained matrix."""
    return verify_evidence_snapshot(path).manifest


def verify_evidence_receipt(path: Path) -> VerifiedEvidence:
    """Resolve a mutable handoff only after verifying its immutable snapshot."""
    absolute = Path(os.path.abspath(path))
    if absolute.is_symlink():
        raise ValidationError(
            "validation evidence receipt must not be a symlink"
        )
    if not absolute.is_file():
        raise ValidationError(
            f"validation evidence receipt is not a regular file: {path}"
        )
    try:
        value = json.loads(absolute.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValidationError(
            f"cannot read validation evidence receipt {path}: {error}"
        ) from error
    if (
        not isinstance(value, dict)
        or set(value)
        != {"version", "identity", "kind", "source", "manifest"}
        or value["version"] != PROTOCOL_VERSION
        or value["kind"] != VALIDATION_EVIDENCE_RECEIPT_KIND
    ):
        raise ValidationError(
            "validation evidence receipt has an unsupported schema"
        )
    identity = value["identity"]
    if (
        not isinstance(identity, dict)
        or set(identity) != {"algorithm", "receipt"}
        or identity["algorithm"] != "sha256"
    ):
        raise ValidationError(
            "validation evidence receipt identity is malformed"
        )
    receipt_sha256 = checked_sha256(
        identity["receipt"], "validation evidence receipt identity"
    )
    provisional = dict(value)
    provisional.pop("identity")
    if receipt_sha256 != canonical_json_sha256(provisional):
        raise ValidationError(
            "validation evidence receipt identity does not match its content"
        )
    source_identity = value["source"]
    if (
        not isinstance(source_identity, dict)
        or set(source_identity)
        != {"runSha256", "evidenceSha256", "matrixSha256"}
    ):
        raise ValidationError(
            "validation evidence receipt source is malformed"
        )
    checked_sha256(
        source_identity["runSha256"], "validation evidence receipt run"
    )
    checked_sha256(
        source_identity["evidenceSha256"],
        "validation evidence receipt evidence",
    )
    checked_sha256(
        source_identity["matrixSha256"],
        "validation evidence receipt matrix",
    )
    manifest = checked_relative_posix_path(
        value["manifest"], "validation evidence receipt manifest"
    )
    source = verify_evidence_snapshot(absolute.parent / manifest)
    if source.report_root.resolve() != absolute.parent.resolve():
        raise ValidationError(
            "validation evidence receipt resolves outside its report root"
        )
    expected = validation_evidence_receipt_value(source)
    if value != expected:
        raise ValidationError(
            "validation evidence receipt disagrees with its immutable source"
        )
    return source


def write_evidence_receipt(out_dir: Path, evidence_path: Path) -> Path:
    """Atomically publish the verified immutable evidence used by this run."""
    source = verify_evidence_snapshot(evidence_path)
    root = out_dir.resolve()
    if source.report_root.resolve() != root:
        raise ValidationError(
            "validation evidence receipt source is outside the output directory"
        )
    value = validation_evidence_receipt_value(source)
    content = (
        json.dumps(value, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")
    destination = out_dir / VALIDATION_EVIDENCE_RECEIPT_NAME
    if destination.is_symlink() or (
        destination.exists() and not destination.is_file()
    ):
        raise ValidationError(
            f"validation evidence receipt is not a regular file: {destination}"
        )
    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            dir=out_dir,
            prefix=".validation-evidence-receipt-",
            delete=False,
        ) as temporary:
            temporary.write(content)
            temporary.flush()
            os.fsync(temporary.fileno())
            temporary_path = Path(temporary.name)
        os.replace(temporary_path, destination)
        temporary_path = None
    except OSError as error:
        raise ValidationError(
            f"cannot write validation evidence receipt {destination}: {error}"
        ) from error
    finally:
        if temporary_path is not None:
            try:
                temporary_path.unlink(missing_ok=True)
            except OSError as error:
                raise ValidationError(
                    "cannot remove temporary validation evidence receipt "
                    f"{temporary_path}: {error}"
                ) from error
    verify_evidence_receipt(destination)
    return destination


def ordered_evidence_delta(before: list, after: list) -> dict:
    """Compare ordered, unique JSON values while exposing set and order drift."""
    def key(value: object) -> str:
        return json.dumps(value, separators=(",", ":"), sort_keys=True)

    before_keys = [key(value) for value in before]
    after_keys = [key(value) for value in after]
    before_set = set(before_keys)
    after_set = set(after_keys)
    return {
        "changed": before != after,
        "before": before,
        "after": after,
        "added": [
            value for value, item_key in zip(after, after_keys)
            if item_key not in before_set
        ],
        "removed": [
            value for value, item_key in zip(before, before_keys)
            if item_key not in after_set
        ],
        "orderChanged": (
            before_set == after_set and before_keys != after_keys
        ),
    }


def evidence_inventory_delta(
    before: list[dict],
    after: list[dict],
    identity_fields: tuple[str, ...],
) -> dict:
    """Compare a verified logical inventory independently of list position."""
    def item_key(item: dict) -> tuple[str, ...]:
        return tuple(str(item[field]) for field in identity_fields)

    before_items = {item_key(item): item for item in before}
    after_items = {item_key(item): item for item in after}
    added = [after_items[key] for key in sorted(after_items.keys() - before_items)]
    removed = [
        before_items[key] for key in sorted(before_items.keys() - after_items)
    ]
    changed = [
        {
            "identity": {
                field: before_items[key][field]
                for field in identity_fields
            },
            "before": before_items[key],
            "after": after_items[key],
        }
        for key in sorted(before_items.keys() & after_items)
        if before_items[key] != after_items[key]
    ]
    return {"added": added, "removed": removed, "changed": changed}


def evidence_findings_delta(before: list[dict], after: list[dict]) -> dict:
    """Compare the verified findings as a multiset."""
    def counted(findings: list[dict]) -> dict[str, tuple[dict, int]]:
        result: dict[str, tuple[dict, int]] = {}
        for finding in findings:
            key = json.dumps(finding, separators=(",", ":"), sort_keys=True)
            previous = result.get(key)
            result[key] = (
                finding,
                1 if previous is None else previous[1] + 1,
            )
        return result

    before_counts = counted(before)
    after_counts = counted(after)
    added = []
    removed = []
    for key in sorted(before_counts.keys() | after_counts.keys()):
        before_count = before_counts.get(key, ({}, 0))[1]
        after_count = after_counts.get(key, ({}, 0))[1]
        if after_count > before_count:
            added.append(
                {
                    "finding": after_counts[key][0],
                    "count": after_count - before_count,
                }
            )
        elif before_count > after_count:
            removed.append(
                {
                    "finding": before_counts[key][0],
                    "count": before_count - after_count,
                }
            )
    return {"added": added, "removed": removed}


def retained_result_outcomes(
    evidence: VerifiedEvidence,
) -> dict[tuple[str, str], dict]:
    """Load semantic outcomes from an already verified evidence graph."""
    outcomes: dict[tuple[str, str], dict] = {}
    for artifact in evidence.matrix["artifacts"]:
        if artifact["kind"] != "backend-result":
            continue
        content = verify_evidence_file(
            evidence.report_root,
            artifact["artifact"],
            artifact["sha256"],
            f"compared backend result {artifact['name']}",
        )
        try:
            record = json.loads(content.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise ValidationError(
                "compared backend result is not JSON"
            ) from error
        if not isinstance(record, dict):
            raise ValidationError("compared backend result is malformed")
        backend = validate_backend_name(
            record.get("backend"), "compared result backend"
        )
        case_id, outcome = checked_record(record, backend)
        key = (backend, case_id)
        if key in outcomes:
            raise ValidationError("compared evidence has duplicate results")
        outcomes[key] = outcome
    return outcomes


def evidence_coverage_claim(coverage: dict) -> dict:
    """Remove explicitly operational telemetry from canonical coverage."""
    claim = json.loads(json.dumps(coverage))
    for consumer in claim["consumers"]:
        consumer["executionAccess"].pop("traceAccessCount")
    return claim


def compare_verified_evidence(
    before: VerifiedEvidence,
    after: VerifiedEvidence,
) -> dict:
    """Classify exact differences between two verified evidence graphs."""
    before_matrix = before.matrix
    after_matrix = after.matrix
    selected_cases = ordered_evidence_delta(
        before_matrix["selectedCases"], after_matrix["selectedCases"]
    )
    backends = ordered_evidence_delta(
        before_matrix["backends"], after_matrix["backends"]
    )
    providers = ordered_evidence_delta(
        before_matrix.get("providers", []),
        after_matrix.get("providers", []),
    )
    before_pairs = [
        {"reference": item["reference"], "candidate": item["candidate"]}
        for item in before_matrix["pairs"]
    ]
    after_pairs = [
        {"reference": item["reference"], "candidate": item["candidate"]}
        for item in after_matrix["pairs"]
    ]
    pair_graph = ordered_evidence_delta(before_pairs, after_pairs)

    inventory_specs = {
        "inputs": ("kind", "name"),
        "products": ("backend", "kind", "name"),
        "tools": ("backend", "kind", "name"),
        "buildInputs": ("backend", "kind", "name"),
        "artifacts": ("kind", "name"),
        "comparisons": ("reference", "candidate"),
        "productBundles": ("provider",),
        "productConsumers": ("backend",),
        "productReceipts": ("backend", "caseId"),
    }
    before_inventories = {
        **before_matrix,
        "comparisons": before_matrix["pairs"],
    }
    after_inventories = {
        **after_matrix,
        "comparisons": after_matrix["pairs"],
    }
    inventories = {
        name: evidence_inventory_delta(
            before_inventories.get(name, []),
            after_inventories.get(name, []),
            fields,
        )
        for name, fields in inventory_specs.items()
    }

    before_outcomes = retained_result_outcomes(before)
    after_outcomes = retained_result_outcomes(after)
    semantic_results: list[dict[str, object]] = []
    for backend, case_id in sorted(before_outcomes.keys() | after_outcomes.keys()):
        before_outcome = before_outcomes.get((backend, case_id))
        after_outcome = after_outcomes.get((backend, case_id))
        if before_outcome == after_outcome:
            continue
        change = (
            "added" if before_outcome is None
            else "removed" if after_outcome is None
            else "changed"
        )
        semantic_results.append(
            {
                "backend": backend,
                "caseId": case_id,
                "change": change,
                "before": before_outcome,
                "after": after_outcome,
            }
        )

    findings = evidence_findings_delta(
        before_matrix["findings"], after_matrix["findings"]
    )
    coverage_before = before_matrix["coverage"]
    coverage_after = after_matrix["coverage"]
    coverage_changed = coverage_before != coverage_after
    coverage_claim_changed = (
        evidence_coverage_claim(coverage_before)
        != evidence_coverage_claim(coverage_after)
    )
    before_telemetry = {
        consumer["backend"]: consumer["executionAccess"]["traceAccessCount"]
        for consumer in coverage_before["consumers"]
    }
    after_telemetry = {
        consumer["backend"]: consumer["executionAccess"]["traceAccessCount"]
        for consumer in coverage_after["consumers"]
    }

    def inventory_changed(name: str) -> bool:
        return any(inventories[name][field] for field in inventories[name])

    contract_inventory_names = {
        "inputs",
        "products",
        "tools",
        "buildInputs",
        "productBundles",
        "productConsumers",
    }
    contract_changed = (
        selected_cases["changed"]
        or backends["changed"]
        or providers["changed"]
        or pair_graph["changed"]
        or any(
            inventory_changed(name) for name in contract_inventory_names
        )
    )
    findings_changed = bool(findings["added"] or findings["removed"])
    receipt_bindings_changed = inventory_changed("productReceipts")
    artifacts_changed = inventory_changed("artifacts")
    comparisons_changed = inventory_changed("comparisons")
    result_counts = {
        change: sum(
            int(item["change"] == change) for item in semantic_results
        )
        for change in ("added", "removed", "changed")
    }
    inventory_counts = {
        name: {
            field: len(delta[field])
            for field in ("added", "removed", "changed")
        }
        for name, delta in inventories.items()
    }
    run_changed = (
        before.manifest["identity"]["run"]
        != after.manifest["identity"]["run"]
    )
    evidence_changed = (
        before.manifest["identity"]["evidence"]
        != after.manifest["identity"]["evidence"]
    )
    portable_claim_changed = (
        run_changed
        or contract_changed
        or bool(semantic_results)
        or coverage_claim_changed
        or findings_changed
        or receipt_bindings_changed
        or comparisons_changed
    )
    classification = {
        "runChanged": run_changed,
        "evidenceChanged": evidence_changed,
        "contractChanged": contract_changed,
        "semanticResultsChanged": bool(semantic_results),
        "semanticObservationsChanged": any(
            item["change"] == "changed" for item in semantic_results
        ),
        "coverageChanged": coverage_changed,
        "coverageClaimChanged": coverage_claim_changed,
        "executionTelemetryChanged": before_telemetry != after_telemetry,
        "findingsChanged": findings_changed,
        "receiptBindingsChanged": receipt_bindings_changed,
        "artifactsChanged": artifacts_changed,
        "comparisonsChanged": comparisons_changed,
        "portableClaimChanged": portable_claim_changed,
    }
    return {
        "version": PROTOCOL_VERSION,
        "before": {
            "run": before.manifest["identity"]["run"],
            "evidence": before.manifest["identity"]["evidence"],
            "matrix": before.manifest["matrix"]["sha256"],
        },
        "after": {
            "run": after.manifest["identity"]["run"],
            "evidence": after.manifest["identity"]["evidence"],
            "matrix": after.manifest["matrix"]["sha256"],
        },
        "classification": classification,
        "equivalence": {
            "portable": not portable_claim_changed,
            "exact": not evidence_changed,
        },
        "summary": {
            "semanticResultAddedCount": result_counts["added"],
            "semanticResultRemovedCount": result_counts["removed"],
            "semanticResultChangedCount": result_counts["changed"],
            "findingAddedCount": sum(
                item["count"] for item in findings["added"]
            ),
            "findingRemovedCount": sum(
                item["count"] for item in findings["removed"]
            ),
            "inventoryCounts": inventory_counts,
        },
        "selectedCases": selected_cases,
        "backends": backends,
        "providers": providers,
        "pairGraph": pair_graph,
        "inventories": inventories,
        "semanticResults": semantic_results,
        "findings": findings,
        "coverage": {"before": coverage_before, "after": coverage_after},
        "executionTelemetry": {
            "before": before_telemetry,
            "after": after_telemetry,
        },
    }


def evidence_comparison_equivalent(
    comparison: dict, level: str
) -> bool:
    """Check a verified comparison at one declared equivalence level."""
    if level == "portable":
        return not comparison["classification"]["portableClaimChanged"]
    if level == "exact":
        return not comparison["classification"]["evidenceChanged"]
    raise ValidationError(f"unknown evidence equivalence level: {level}")


def render_evidence_comparison(comparison: dict) -> list[str]:
    """Render the stable evidence comparison report for humans."""
    before = comparison["before"]
    after = comparison["after"]
    classification = comparison["classification"]

    def state(field: str) -> str:
        return "changed" if classification[field] else "same"

    lines = [
        f"evidence comparison: {before['evidence']} -> {after['evidence']}",
        "equivalence: "
        f"portable {'same' if comparison['equivalence']['portable'] else 'changed'}, "
        f"exact {'same' if comparison['equivalence']['exact'] else 'changed'}",
        "classification: "
        f"contract {state('contractChanged')}, "
        f"semantic results {state('semanticResultsChanged')}, "
        f"coverage claim {state('coverageClaimChanged')}, "
        f"telemetry {state('executionTelemetryChanged')}, "
        f"findings {state('findingsChanged')}, "
        f"exact evidence {state('evidenceChanged')}",
        "bindings: "
        f"run identity {state('runChanged')}, "
        f"receipts {state('receiptBindingsChanged')}, "
        f"comparisons {state('comparisonsChanged')}, "
        f"artifacts {state('artifactsChanged')}",
    ]
    summary = comparison["summary"]
    lines.append(
        "semantic results: "
        f"+{summary['semanticResultAddedCount']} "
        f"-{summary['semanticResultRemovedCount']} "
        f"~{summary['semanticResultChangedCount']}"
    )
    for result in comparison["semanticResults"]:
        lines.append(
            f"semantic {result['change']}: "
            f"{result['backend']}/{result['caseId']}"
        )
    for name in ("selectedCases", "backends", "providers", "pairGraph"):
        delta = comparison[name]
        if delta["changed"]:
            lines.append(
                f"{name}: +{len(delta['added'])} "
                f"-{len(delta['removed'])} "
                f"order={'changed' if delta['orderChanged'] else 'same'}"
            )
    for name, counts in summary["inventoryCounts"].items():
        if any(counts.values()):
            lines.append(
                f"{name}: +{counts['added']} -{counts['removed']} "
                f"~{counts['changed']}"
            )
    lines.append(
        "findings: "
        f"+{summary['findingAddedCount']} "
        f"-{summary['findingRemovedCount']}"
    )
    return lines


def build_product_providers(
    context: BuildContext,
    providers: tuple[ProductProvider, ...],
) -> tuple[ProductProviderRun, ...]:
    """Build each configured provider exactly once."""
    if context.run_context is None:
        raise ValidationError("product providers require a validation run context")
    runs: list[ProductProviderRun] = []
    names: set[str] = set()
    for provider in providers:
        name = validate_backend_name(provider.name, "product provider")
        if name in names:
            raise ValidationError(f"product provider configured twice: {name}")
        names.add(name)
        provider_run = provider.build(context)
        if provider_run.provider != name:
            raise ValidationError(
                f"provider {name} returned provider run {provider_run.provider}"
            )
        if any(product.backend != name for product in provider_run.products):
            raise ValidationError(
                f"product provider {name} returned foreign-owned products"
            )
        if any(tool.backend != name for tool in provider_run.tools):
            raise ValidationError(
                f"product provider {name} returned foreign-owned tools"
            )
        if any(item.backend != name for item in provider_run.build_inputs):
            raise ValidationError(
                f"product provider {name} returned foreign-owned build inputs"
            )
        for artifact in provider_run.artifacts:
            artifact_owner, _, _ = validation_artifact_scope(
                artifact.kind,
                artifact.name,
                [name],
                context.run_context.selected,
            )
            if artifact_owner != name or artifact.kind == "backend-result":
                raise ValidationError(
                    f"product provider {name} returned foreign execution evidence"
                )
        if any(
            finding.backend not in (None, name)
            or (
                finding.case_id is not None
                and finding.case_id not in context.run_context.selected
            )
            for finding in provider_run.findings
        ):
            raise ValidationError(
                f"product provider {name} returned foreign findings"
            )
        checked_bundle = product_bundle_from_json(
            provider_run.bundle.to_json(),
            [name],
            provider_run.products,
            context.run_context.selected,
            f"product provider {name}",
        )
        if checked_bundle != provider_run.bundle:
            raise ValidationError(
                f"product provider {name} returned a malformed bundle"
            )
        manifests = [
            product for product in provider_run.products
            if product.backend == name
            and product.kind == RESERVED_PRODUCT_KIND
        ]
        if len(manifests) != 1:
            raise ValidationError(
                f"product provider {name} requires one bundle manifest"
            )
        manifest = manifests[0]
        captured_manifest, content = validation_product_and_content_from_file(
            name,
            ProductDeclaration(manifest.kind, manifest.name),
            context.out_dir,
        )
        if captured_manifest != manifest:
            raise ValidationError(
                f"product provider {name} bundle manifest changed after build"
            )
        reconstructed = product_bundle_from_manifest(
            name,
            checked_bundle.contract,
            content,
            tuple(provider_run.products),
            context.run_context.selected,
            f"product provider {name} manifest",
        )
        if reconstructed != checked_bundle:
            raise ValidationError(
                f"product provider {name} manifest disagrees with its bundle"
            )
        runs.append(provider_run)
    return tuple(runs)


def verify_product_provider_run(
    context: RunContext, provider_run: ProductProviderRun, phase: str
) -> None:
    for product in provider_run.products:
        captured = validation_product_from_file(
            provider_run.provider,
            ProductDeclaration(product.kind, product.name),
            context.out_dir,
        )
        if captured != product:
            raise ValidationError(
                f"{provider_run.provider} products changed {phase}: "
                f"{product.kind}:{product.name}"
            )


def validate_matrix(
    context: RunContext,
    pairs: list[tuple[BackendAdapter, BackendAdapter]],
    provider_runs: tuple[ProductProviderRun, ...] = (),
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

    provider_run_by_name: dict[str, ProductProviderRun] = {}
    for provider_run in provider_runs:
        provider_name = validate_backend_name(
            provider_run.provider, "product provider"
        )
        if provider_name in provider_run_by_name:
            raise ValidationError(
                f"product provider ran more than once: {provider_name}"
            )
        if provider_name in adapters:
            raise ValidationError(
                f"product provider and backend names overlap: {provider_name}"
            )
        if provider_run.bundle.provider != provider_name:
            raise ValidationError(
                f"provider run {provider_name} returned a foreign bundle"
            )
        if context.product_bundles.get(provider_name) != provider_run.bundle:
            raise ValidationError(
                f"run context disagrees with product provider {provider_name}"
            )
        provider_run_by_name[provider_name] = provider_run

    product_consumers: list[ProductConsumer] = []
    used_providers: set[str] = set()
    for name, adapter in adapters.items():
        requirement = getattr(adapter, "product_provider", None)
        if requirement is None:
            continue
        if not isinstance(requirement, ProductProviderRequirement):
            raise ValidationError(
                f"backend {name} has malformed product provider requirement"
            )
        provider_run = provider_run_by_name.get(requirement.provider)
        if provider_run is None:
            raise ValidationError(
                f"backend {name} requires missing product provider "
                f"{requirement.provider}"
            )
        bundle = provider_run.bundle
        if requirement.contract != bundle.contract:
            raise ValidationError(
                f"backend {name} product contract disagrees with provider "
                f"{bundle.provider}"
            )
        product_consumers.append(
            ProductConsumer(
                name,
                bundle.provider,
                requirement.contract,
                bundle.bundle_sha256,
            )
        )
        used_providers.add(bundle.provider)
    unused_providers = sorted(provider_run_by_name.keys() - used_providers)
    if unused_providers:
        raise ValidationError(
            "unused product provider(s): " + ", ".join(unused_providers)
        )

    backend_runs: dict[str, BackendRun] = {}
    backend_findings: dict[str, list[ValidationFinding]] = {}
    product_receipts: list[ProductReceipt] = []
    all_findings: list[ValidationFinding] = [
        finding
        for provider_run in provider_runs
        for finding in provider_run.findings
    ]
    for name, adapter in adapters.items():
        requirement = getattr(adapter, "product_provider", None)
        provider_run = (
            provider_run_by_name[requirement.provider]
            if isinstance(requirement, ProductProviderRequirement)
            else None
        )
        if provider_run is not None:
            verify_product_provider_run(
                context, provider_run, f"before {name} execution"
            )
        backend_run = adapter.execute(context)
        if provider_run is not None:
            verify_product_provider_run(
                context, provider_run, f"during {name} execution"
            )
        if backend_run.backend != name:
            raise ValidationError(
                f"adapter {name} returned backend run {backend_run.backend}"
            )
        if any(product.backend != name for product in backend_run.products):
            raise ValidationError(
                f"backend {name} returned foreign-owned products"
            )
        if any(tool.backend != name for tool in backend_run.tools):
            raise ValidationError(
                f"backend {name} returned foreign-owned tools"
            )
        if any(item.backend != name for item in backend_run.build_inputs):
            raise ValidationError(
                f"backend {name} returned foreign-owned build inputs"
            )
        for artifact in backend_run.artifacts:
            artifact_owner, _, _ = validation_artifact_scope(
                artifact.kind,
                artifact.name,
                [name],
                context.selected,
            )
            if artifact_owner != name:
                raise ValidationError(
                    f"backend {name} returned foreign-owned artifacts"
                )
        if provider_run is not None and (
            backend_run.products or backend_run.build_inputs
        ):
            raise ValidationError(
                f"product consumer {name} returned build-owned evidence"
            )
        findings = list(backend_run.findings)
        findings.extend(
            result_domain_findings(
                backend_run.results, name, backend_run.expected_cases
            )
        )
        audit = adapter.audit(context, backend_run)
        findings.extend(audit.findings)
        if provider_run is not None:
            for case_id, record in sorted(backend_run.results.items()):
                product_receipts.append(
                    checked_product_bundle_receipt(
                        record, name, case_id, provider_run.bundle
                    )
                )
        backend_runs[name] = backend_run
        backend_findings[name] = findings
        all_findings.extend(findings)

        for case_id in context.selected:
            record = backend_run.results.get(case_id)
            if record is not None:
                backend_run.artifacts.append(
                    write_artifact(context.out_dir, case_id, name, record)
                )

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
    products += tuple(
        product
        for provider_run in provider_runs
        for product in provider_run.products
    )
    tools = tuple(
        tool
        for backend_run in backend_runs.values()
        for tool in backend_run.tools
    )
    tools += tuple(
        tool
        for provider_run in provider_runs
        for tool in provider_run.tools
    )
    build_inputs = tuple(
        item
        for backend_run in backend_runs.values()
        for item in backend_run.build_inputs
    )
    build_inputs += tuple(
        item
        for provider_run in provider_runs
        for item in provider_run.build_inputs
    )
    artifacts = tuple(
        artifact
        for backend_run in backend_runs.values()
        for artifact in backend_run.artifacts
    )
    artifacts += tuple(
        artifact
        for provider_run in provider_runs
        for artifact in provider_run.artifacts
    )
    write_matrix_artifact(
        context,
        list(adapters),
        pair_results,
        all_findings,
        products,
        tools,
        artifacts,
        build_inputs,
        provider_runs,
        tuple(product_consumers),
        tuple(product_receipts),
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
