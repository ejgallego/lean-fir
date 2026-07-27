#!/usr/bin/env python3
"""Generic content-addressed envelopes for independently checked evidence."""

from __future__ import annotations

import json
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from validation_harness import (
    PROTOCOL_VERSION,
    ValidationError,
    canonical_json_sha256,
    checked_sha256,
    retain_evidence_bundle,
)


RecordValidator = Callable[[object], dict]


@dataclass(frozen=True)
class EnvelopeSpec:
    kind: str
    contract_kind: str
    contract_fields: tuple[str, ...]
    record_id_field: str = "caseId"


def validate_spec(spec: EnvelopeSpec) -> EnvelopeSpec:
    names = [
        spec.kind,
        spec.contract_kind,
        spec.record_id_field,
        *spec.contract_fields,
    ]
    if any(
        not isinstance(name, str)
        or not name
        or name != name.strip()
        or "\n" in name
        for name in names
    ):
        raise ValidationError("attestation envelope spec names must be nonempty")
    if (
        not spec.contract_fields
        or len(spec.contract_fields) != len(set(spec.contract_fields))
        or spec.record_id_field not in spec.contract_fields
    ):
        raise ValidationError(
            "attestation envelope contract fields must be unique and include "
            "the record ID"
        )
    return spec


def record_id(spec: EnvelopeSpec, record: object) -> str:
    if not isinstance(record, dict):
        raise ValidationError("attestation envelope record must be an object")
    value = record.get(spec.record_id_field)
    if (
        not isinstance(value, str)
        or not value
        or value != value.strip()
        or "\n" in value
    ):
        raise ValidationError(
            f"attestation envelope {spec.record_id_field} must be nonempty"
        )
    return value


def with_record_identity(record: object) -> dict:
    if not isinstance(record, dict):
        raise ValidationError("attestation envelope record must be an object")
    if "identity" in record:
        raise ValidationError("attestation envelope record already has an identity")
    return {
        **record,
        "identity": {
            "algorithm": "sha256",
            "record": canonical_json_sha256(record),
        },
    }


def verify_record_identity(record: object, context: str) -> dict:
    if not isinstance(record, dict):
        raise ValidationError(f"{context}: record must be an object")
    identity = record.get("identity")
    if (
        not isinstance(identity, dict)
        or set(identity) != {"algorithm", "record"}
        or identity["algorithm"] != "sha256"
    ):
        raise ValidationError(f"{context}: record identity is malformed")
    digest = checked_sha256(identity["record"], f"{context} identity")
    provisional = dict(record)
    provisional.pop("identity")
    if digest != canonical_json_sha256(provisional):
        raise ValidationError(
            f"{context}: record identity does not match its content"
        )
    return record


def _validated_records(
    spec: EnvelopeSpec,
    records: object,
    validate_record: RecordValidator,
    *,
    require_ordered: bool,
) -> list[dict]:
    validate_spec(spec)
    if not isinstance(records, list) or not records:
        raise ValidationError("attestation envelope records must be nonempty")
    validated: list[dict] = []
    ids: list[str] = []
    for raw_record in records:
        current_id = record_id(spec, raw_record)
        record = verify_record_identity(
            raw_record,
            f"attestation envelope {current_id}",
        )
        before_validation = canonical_json_sha256(record)
        validated_record = validate_record(record)
        if (
            validated_record is not record
            or canonical_json_sha256(record) != before_validation
        ):
            raise ValidationError(
                "attestation envelope record validator must preserve its input"
            )
        validated.append(record)
        ids.append(current_id)
    if len(ids) != len(set(ids)):
        raise ValidationError("attestation envelope repeats a record ID")
    if require_ordered and ids != sorted(ids):
        raise ValidationError(
            "attestation envelope records must be sorted by record ID"
        )
    return validated


def contract_artifact(spec: EnvelopeSpec, records: list[dict]) -> dict:
    validate_spec(spec)
    ordered = sorted(records, key=lambda record: record_id(spec, record))
    projected: list[dict] = []
    for record in ordered:
        missing = [
            field for field in spec.contract_fields if field not in record
        ]
        if missing:
            raise ValidationError(
                f"attestation envelope contract omits fields {missing!r}"
            )
        projected.append(
            {field: record[field] for field in spec.contract_fields}
        )
    return {
        "version": PROTOCOL_VERSION,
        "kind": spec.contract_kind,
        "records": projected,
    }


def build_envelope(
    spec: EnvelopeSpec,
    records: list[dict],
    validate_record: RecordValidator,
) -> dict:
    validated = _validated_records(
        spec,
        records,
        validate_record,
        require_ordered=False,
    )
    ordered = sorted(validated, key=lambda record: record_id(spec, record))
    contract_sha256 = canonical_json_sha256(contract_artifact(spec, ordered))
    provisional = {
        "version": PROTOCOL_VERSION,
        "kind": spec.kind,
        "contractSha256": contract_sha256,
        "records": ordered,
    }
    return {
        "version": PROTOCOL_VERSION,
        "identity": {
            "algorithm": "sha256",
            "contract": contract_sha256,
            "evidence": canonical_json_sha256(provisional),
        },
        "kind": spec.kind,
        "records": ordered,
    }


def verify_envelope_value(
    value: object,
    spec: EnvelopeSpec,
    validate_record: RecordValidator,
) -> dict:
    validate_spec(spec)
    if (
        not isinstance(value, dict)
        or set(value) != {"version", "identity", "kind", "records"}
        or value["version"] != PROTOCOL_VERSION
        or value["kind"] != spec.kind
    ):
        raise ValidationError("attestation envelope has an unsupported schema")
    identity = value["identity"]
    if (
        not isinstance(identity, dict)
        or set(identity) != {"algorithm", "contract", "evidence"}
        or identity["algorithm"] != "sha256"
    ):
        raise ValidationError("attestation envelope identity is malformed")
    contract_sha256 = checked_sha256(
        identity["contract"], "attestation envelope contract identity"
    )
    evidence_sha256 = checked_sha256(
        identity["evidence"], "attestation envelope evidence identity"
    )
    records = _validated_records(
        spec,
        value["records"],
        validate_record,
        require_ordered=True,
    )
    actual_contract_sha256 = canonical_json_sha256(
        contract_artifact(spec, records)
    )
    if contract_sha256 != actual_contract_sha256:
        raise ValidationError(
            "attestation envelope contract identity does not match its content"
        )
    provisional = {
        "version": PROTOCOL_VERSION,
        "kind": spec.kind,
        "contractSha256": contract_sha256,
        "records": records,
    }
    if evidence_sha256 != canonical_json_sha256(provisional):
        raise ValidationError(
            "attestation envelope evidence identity does not match its content"
        )
    return value


def read_envelope(
    path: Path,
    spec: EnvelopeSpec,
    validate_record: RecordValidator,
) -> dict:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except OSError as error:
        raise ValidationError(
            f"cannot read attestation envelope {path}: {error}"
        ) from error
    except json.JSONDecodeError as error:
        raise ValidationError(
            f"attestation envelope is not valid JSON: {path}"
        ) from error
    return verify_envelope_value(value, spec, validate_record)


def envelope_bytes(envelope: dict) -> bytes:
    return (
        json.dumps(envelope, indent=2, sort_keys=True) + "\n"
    ).encode("utf-8")


def write_retained_envelope(
    out_dir: Path,
    live_name: str,
    envelope: dict,
    spec: EnvelopeSpec,
    validate_record: RecordValidator,
) -> str:
    if (
        not isinstance(live_name, str)
        or not live_name
        or Path(live_name).name != live_name
    ):
        raise ValidationError(
            "attestation envelope live name must be one file name"
        )
    verified = verify_envelope_value(envelope, spec, validate_record)
    content = envelope_bytes(verified)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / live_name).write_bytes(content)
    return retain_evidence_bundle(
        out_dir,
        verified["identity"]["contract"],
        verified["identity"]["evidence"],
        content,
    )
