#!/usr/bin/env python3

import contextlib
import fcntl
import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import validate_interpreters as harness
import record_backend_comparisons as comparison_attestations
import record_direct_native_ir as native_ir
import validation_attestation as attestation
import validation_coverage_index as coverage_index
import validation_harness as core
import validation_lcnf as lcnf


def success(case_id: str, backend: str, value: int = 42) -> dict:
    return {
        "version": 3,
        "caseId": case_id,
        "backend": backend,
        "diagnostics": [],
        "outcome": {
            "success": {
                "observation": {
                    "termination": {"returned": {"value": {"nat": {"value": str(value)}}}},
                    "stdout": "",
                    "stderr": "",
                    "effects": [],
                }
            }
        },
    }


def finding_messages(findings: list[harness.ValidationFinding]) -> list[str]:
    return [
        (f"{finding.case_id}: " if finding.case_id is not None else "")
        + finding.message
        for finding in findings
    ]


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True) + "\n").encode("utf-8")


def config_input(
    kind: str, name: str, value: dict
) -> harness.ValidationInput:
    content = json_bytes(value)
    return harness.ValidationInput(
        kind, name, harness.sha256_bytes(content), content
    )


def fixture_provider_config(
    name: str,
    contract: harness.ProductContract,
    bundle_manifest: str = "bundle.json",
) -> dict:
    python = Path(sys.executable).name
    return {
        "version": 3,
        "name": name,
        "contract": contract.to_json(),
        "buildCommand": [python, "-c", "pass"],
        "bundleManifest": bundle_manifest,
        "buildTools": [
            {
                "kind": "build-launcher",
                "name": "python",
                "command": python,
            }
        ],
    }


def fixture_consumer_config(
    name: str,
    provider: str,
    contract: harness.ProductContract,
) -> dict:
    value = fixture_adapter_config(name)
    value["productProvider"] = {
        "name": provider,
        "contract": contract.to_json(),
    }
    return value


def fixture_adapter_config(name: str) -> dict:
    python = Path(sys.executable).name
    return {
        "name": name,
        "runCommand": [python, "-c", "pass"],
        "resultDomain": "selected",
        "tools": [
            {
                "kind": "engine",
                "name": "python",
                "command": python,
            }
        ],
    }


def descriptor(
    case_id: str,
    *,
    tags: list[str] | None = None,
    forms: list[str] | None = None,
    executed_forms: list[str] | None = None,
    executed_form_counts: list[dict] | None = None,
    required_executed_form_trace: list[str] | None = None,
    required_administrative_step_kinds: list[str] | None = None,
    externals: list[str] | None = None,
    executed_externals: list[str] | None = None,
    executed_external_counts: list[dict] | None = None,
    required_executed_external_trace: list[str] | None = None,
    effect_projections: list[dict] | None = None,
) -> dict:
    item = {
        "version": 3,
        "id": case_id,
        "entry": f"Fir.Validation.Source.{case_id}",
        "dependencies": [],
        "args": [{"nat": {"value": "42"}}],
        "argSchemas": ["nat"],
        "argumentAliases": [],
        "nestedArgumentAliases": [],
        "resultSchema": "nat",
        "tags": tags or ["quick"],
        "fuel": 1000,
        "provenance": {
            "suite": "fir",
            "path": "Fir/Validation/Corpus.lean",
            "revision": "",
            "note": "validation corpus",
        },
        "requiredLcnfForms": forms or ["return"],
        "requiredExecutedLcnfForms": executed_forms or [],
        "requiredExecutedLcnfFormCounts": executed_form_counts or [],
        "requiredExecutedLcnfFormTrace": required_executed_form_trace,
        "requiredAdministrativeStepKinds": (
            required_administrative_step_kinds or []
        ),
        "requiredExternals": externals or [],
        "requiredExecutedExternals": executed_externals or [],
        "requiredExecutedExternalCounts": executed_external_counts or [],
        "requiredExecutedExternalTrace": required_executed_external_trace,
        "effectProjections": effect_projections or [],
    }
    return item


def with_form_diagnostics(
    record: dict,
    *,
    static: str | None = None,
    executed: str | None = None,
    executed_counts: str | None = "__auto__",
    executed_form_trace: str | None = "__auto__",
    executed_step_trace: str | None = "__auto__",
    steps: str | None = "__auto__",
    static_externals: str | None = "",
    missing_static_externals: str | None = "",
    executed_externals: str | None = "",
    executed_external_counts: str | None = "__auto__",
    executed_external_trace: str | None = "__auto__",
    missing_executed_externals: str | None = "",
) -> dict:
    diagnostics = []
    if static is not None:
        diagnostics.append({"key": "lcnf-forms", "value": static})
    if executed is not None:
        diagnostics.append({"key": "executed-lcnf-forms", "value": executed})
    if executed_counts == "__auto__":
        if executed is not None:
            forms = sorted(
                {
                    form.strip()
                    for form in executed.split(",")
                    if form.strip()
                }
            )
            diagnostics.append(
                {
                    "key": "executed-lcnf-form-counts",
                    "value": json.dumps(
                        [{"form": form, "count": 1} for form in forms],
                        separators=(",", ":"),
                    ),
                }
            )
    elif executed_counts is not None:
        diagnostics.append(
            {"key": "executed-lcnf-form-counts", "value": executed_counts}
        )
    form_trace_for_steps: list[str] | None = None
    if executed_form_trace == "__auto__":
        form_trace: list[str] | None = None
        if executed_counts is not None and executed_counts != "__auto__":
            try:
                form_count_items = json.loads(executed_counts)
            except (TypeError, json.JSONDecodeError):
                form_count_items = None
            if (
                isinstance(form_count_items, list)
                and all(
                    isinstance(item, dict)
                    and set(item) == {"form", "count"}
                    and isinstance(item["form"], str)
                    and item["form"]
                    and isinstance(item["count"], int)
                    and not isinstance(item["count"], bool)
                    and item["count"] > 0
                    for item in form_count_items
                )
            ):
                form_trace = [
                    item["form"]
                    for item in form_count_items
                    for _ in range(item["count"])
                ]
        if form_trace is None and executed is not None:
            form_trace = list(
                dict.fromkeys(
                    form.strip()
                    for form in executed.split(",")
                    if form.strip()
                )
            )
        if form_trace is not None:
            form_trace_for_steps = form_trace
            diagnostics.append(
                {
                    "key": "executed-lcnf-form-trace",
                    "value": json.dumps(form_trace, separators=(",", ":")),
                }
            )
    elif executed_form_trace is not None:
        try:
            parsed_form_trace = json.loads(executed_form_trace)
        except (TypeError, json.JSONDecodeError):
            parsed_form_trace = None
        if isinstance(parsed_form_trace, list) and all(
            isinstance(form, str) and form for form in parsed_form_trace
        ):
            form_trace_for_steps = parsed_form_trace
        diagnostics.append(
            {
                "key": "executed-lcnf-form-trace",
                "value": executed_form_trace,
            }
        )
    if form_trace_for_steps is None and executed is not None:
        form_trace_for_steps = list(
            dict.fromkeys(
                form.strip()
                for form in executed.split(",")
                if form.strip()
            )
        )
    emitted_step_trace: list[str] | None = None
    if executed_step_trace == "__auto__":
        if form_trace_for_steps is not None:
            emitted_step_trace = [
                f"form:{form}" for form in form_trace_for_steps
            ]
            if not emitted_step_trace:
                emitted_step_trace = ["admin:yield-done"]
            if (
                steps is not None
                and steps != "__auto__"
                and steps.isdecimal()
                and int(steps) > len(emitted_step_trace)
            ):
                emitted_step_trace.extend(
                    ["admin:yield-done"]
                    * (int(steps) - len(emitted_step_trace))
                )
            diagnostics.append(
                {
                    "key": "executed-step-trace",
                    "value": json.dumps(
                        emitted_step_trace, separators=(",", ":")
                    ),
                }
            )
    elif executed_step_trace is not None:
        try:
            parsed_step_trace = json.loads(executed_step_trace)
        except (TypeError, json.JSONDecodeError):
            parsed_step_trace = None
        if isinstance(parsed_step_trace, list) and all(
            isinstance(kind, str) and kind for kind in parsed_step_trace
        ):
            emitted_step_trace = parsed_step_trace
        diagnostics.append(
            {"key": "executed-step-trace", "value": executed_step_trace}
        )
    resolved_steps = steps
    if steps == "__auto__":
        resolved_steps = str(max(1, len(emitted_step_trace or [])))
    if resolved_steps is not None:
        diagnostics.append(
            {"key": "interpreter-steps", "value": resolved_steps}
        )
    if static_externals is not None:
        diagnostics.append({"key": "externals", "value": static_externals})
    if missing_static_externals is not None:
        diagnostics.append(
            {"key": "missing-externals", "value": missing_static_externals}
        )
    if executed_externals is not None:
        diagnostics.append({"key": "executed-externals", "value": executed_externals})
    if executed_external_counts == "__auto__":
        if executed_externals is not None:
            externals = sorted(
                {
                    external.strip()
                    for external in executed_externals.split(",")
                    if external.strip()
                }
            )
            diagnostics.append(
                {
                    "key": "executed-external-counts",
                    "value": json.dumps(
                        [
                            {"external": external, "count": 1}
                            for external in externals
                        ],
                        separators=(",", ":"),
                    ),
                }
            )
    elif executed_external_counts is not None:
        diagnostics.append(
            {
                "key": "executed-external-counts",
                "value": executed_external_counts,
            }
        )
    if executed_external_trace == "__auto__":
        trace: list[str] | None = None
        if (
            executed_external_counts is not None
            and executed_external_counts != "__auto__"
        ):
            try:
                count_items = json.loads(executed_external_counts)
            except (TypeError, json.JSONDecodeError):
                count_items = None
            if (
                isinstance(count_items, list)
                and all(
                    isinstance(item, dict)
                    and set(item) == {"external", "count"}
                    and isinstance(item["external"], str)
                    and item["external"]
                    and isinstance(item["count"], int)
                    and not isinstance(item["count"], bool)
                    and item["count"] > 0
                    for item in count_items
                )
            ):
                trace = [
                    item["external"]
                    for item in count_items
                    for _ in range(item["count"])
                ]
        if trace is None and executed_externals is not None:
            trace = list(
                dict.fromkeys(
                    external.strip()
                    for external in executed_externals.split(",")
                    if external.strip()
                )
            )
        if trace is not None:
            diagnostics.append(
                {
                    "key": "executed-external-trace",
                    "value": json.dumps(trace, separators=(",", ":")),
                }
            )
    elif executed_external_trace is not None:
        diagnostics.append(
            {
                "key": "executed-external-trace",
                "value": executed_external_trace,
            }
        )
    if missing_executed_externals is not None:
        diagnostics.append(
            {
                "key": "missing-executed-externals",
                "value": missing_executed_externals,
            }
        )
    record["diagnostics"] = diagnostics
    return record


class HarnessTests(unittest.TestCase):
    def test_generic_core_does_not_own_lcnf_execution_or_coverage(self) -> None:
        self.assertFalse(hasattr(core, "LcnfAdapter"))
        self.assertFalse(hasattr(core, "coverage_report"))
        self.assertFalse(hasattr(core, "NativeAdapter"))
        self.assertFalse(hasattr(core, "ROOT"))
        self.assertIs(harness.LcnfAdapter, lcnf.LcnfAdapter)
        self.assertIs(harness.coverage_report, lcnf.coverage_report)

    def test_corpus_manifest_comes_from_the_selected_backend(self) -> None:
        expected = [descriptor("case")]

        class ManifestAdapter:
            name = "fixture-corpus"

            def manifest(self) -> list[dict]:
                return expected

        self.assertIs(harness.corpus_manifest(ManifestAdapter()), expected)

        class NoManifestAdapter:
            name = "no-manifest"

        with self.assertRaisesRegex(
            harness.ValidationError,
            "validation corpus backend no-manifest does not provide a manifest",
        ):
            harness.corpus_manifest(NoManifestAdapter())

    def test_generic_manifest_preserves_but_does_not_require_lcnf_extension(self) -> None:
        item = descriptor(
            "case",
            effect_projections=[
                {
                    "external": "Effect.record",
                    "operation": "validation.record",
                    "argSchemas": ["nat"],
                    "resultSchema": "nat",
                }
            ],
        )
        for field in lcnf.LCNF_MANIFEST_FIELDS:
            del item[field]
        item["futureBackendPolicy"] = {"engine": "v8"}
        parsed = core.manifest_from_output(
            json.dumps(item), ["native", "--manifest"]
        )
        self.assertEqual(parsed[0]["futureBackendPolicy"], {"engine": "v8"})
        self.assertEqual(parsed[0]["effectProjections"], item["effectProjections"])
        with self.assertRaisesRegex(
            harness.ValidationError, "missing requiredAdministrativeStepKinds"
        ):
            lcnf.prepare_manifest(parsed)

        unsafe = dict(item)
        unsafe["id"] = "../case"
        with self.assertRaisesRegex(
            harness.ValidationError, "case ID: name must use lowercase"
        ):
            core.manifest_from_output(
                json.dumps(unsafe), ["native", "--manifest"]
            )

    def test_equal_successes(self) -> None:
        equal, _, _ = harness.compare_success(success("case", "native"), success("case", "lcnf"))
        self.assertTrue(equal)

    def test_semantic_mismatch(self) -> None:
        equal, _, _ = harness.compare_success(
            success("case", "native", 41), success("case", "lcnf", 42)
        )
        self.assertFalse(equal)

    def test_generic_backend_comparison_uses_protocol_observations(self) -> None:
        manifest = {"case": descriptor("case")}
        comparisons, findings = harness.compare_backend_results(
            manifest,
            ["case"],
            "native",
            {"case": success("case", "native", 41)},
            "v8",
            {"case": success("case", "v8", 42)},
        )
        self.assertEqual(comparisons[0]["reference"], "native")
        self.assertEqual(comparisons[0]["candidate"], "v8")
        self.assertFalse(comparisons[0]["equal"])
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].phase, "comparison")
        self.assertEqual(findings[0].case_id, "case")
        self.assertIn("native=", findings[0].message)
        self.assertIn("v8=", findings[0].message)

    def test_generic_comparison_skips_only_explicitly_blocked_cases(self) -> None:
        manifest = {"case": descriptor("case")}
        comparisons, findings = harness.compare_backend_results(
            manifest,
            ["case"],
            "native",
            {"case": success("case", "native")},
            "lcnf",
            {"case": success("case", "lcnf")},
            {"case"},
        )
        self.assertEqual(comparisons, [])
        self.assertEqual(findings, [])

    def test_result_domain_is_configurable_per_backend_run(self) -> None:
        results = {
            "selected": success("selected", "v8"),
            "unknown": success("unknown", "v8"),
        }
        self.assertEqual(
            [
                finding.to_json()
                for finding in harness.result_domain_findings(
                    results, "v8", ["selected", "missing"]
                )
            ],
            [
                {
                    "phase": "result-domain",
                    "message": "backend returned an unknown case",
                    "backend": "v8",
                    "caseId": "unknown",
                },
                {
                    "phase": "result-domain",
                    "message": "backend omitted the expected case",
                    "backend": "v8",
                    "caseId": "missing",
                },
            ],
        )

    def test_effect_mismatch_is_semantic(self) -> None:
        native = success("case", "native")
        native["outcome"]["success"]["observation"]["effects"] = [
            {
                "operation": "validation.record",
                "args": [{"nat": {"value": "7"}}],
                "result": {"nat": {"value": "8"}},
            }
        ]
        equal, _, _ = harness.compare_success(native, success("case", "lcnf"))
        self.assertFalse(equal)

    def test_effect_order_is_semantic(self) -> None:
        native = success("case", "native")
        candidate = success("case", "lcnf")
        effects = [
            {
                "operation": "validation.record",
                "args": [{"nat": {"value": str(value)}}],
                "result": {"nat": {"value": str(value + 1)}},
            }
            for value in (7, 8)
        ]
        native["outcome"]["success"]["observation"]["effects"] = effects
        candidate["outcome"]["success"]["observation"]["effects"] = list(
            reversed(effects)
        )
        equal, _, _ = harness.compare_success(native, candidate)
        self.assertFalse(equal)

    def test_duplicate_result_rejected(self) -> None:
        record = success("case", "native")
        with self.assertRaises(harness.ValidationError):
            harness.result_map([record, record], "native")

    def test_wrong_version_rejected(self) -> None:
        record = success("case", "native")
        record["version"] = 4
        with self.assertRaises(harness.ValidationError):
            harness.checked_record(record, "native")

    def test_backend_failure_is_not_semantics(self) -> None:
        record = success("case", "lcnf")
        record["outcome"] = {"outOfFuel": {"fuel": 10}}
        with self.assertRaises(harness.ValidationError):
            harness.success_observation(record)

    def test_malformed_jsonl_rejected(self) -> None:
        with self.assertRaises(harness.ValidationError):
            harness.records_from_output("{not-json}\n", ["fake-backend"])

    def test_manifest_is_canonicalized(self) -> None:
        second = descriptor(
            "z-case",
            tags=["slow", "quick"],
            forms=["return", "inc"],
            executed_forms=["return", "fap"],
            executed_form_counts=[
                {"form": "return", "minimum": 2, "maximum": None},
                {"form": "fap", "minimum": 1, "maximum": 3},
            ],
            required_executed_form_trace=["return", "fap", "return"],
            required_administrative_step_kinds=[
                "admin:yield-done",
                "admin:invoke-name",
            ],
            externals=["Nat.add", "ByteArray.size"],
            executed_externals=["Nat.add", "ByteArray.size"],
            executed_external_counts=[
                {"external": "Nat.add", "minimum": 2, "maximum": None},
                {"external": "ByteArray.size", "minimum": 1, "maximum": 1},
            ],
            required_executed_external_trace=[
                "Nat.add",
                "ByteArray.size",
                "Nat.add",
            ],
            effect_projections=[
                {
                    "external": "Nat.add",
                    "operation": "validation.z",
                    "argSchemas": ["nat"],
                    "resultSchema": "nat",
                },
                {
                    "external": "ByteArray.size",
                    "operation": "validation.a",
                    "argSchemas": [],
                    "resultSchema": None,
                },
            ],
        )
        first = descriptor("a-case")
        output = "compiler noise\n" + json.dumps(second) + "\n" + json.dumps(first) + "\n"
        manifest = harness.manifest_from_output(output, ["native", "--manifest"])
        self.assertEqual([item["id"] for item in manifest], ["a-case", "z-case"])
        self.assertEqual(manifest[1]["tags"], ["quick", "slow"])
        self.assertEqual(manifest[1]["requiredLcnfForms"], ["inc", "return"])
        self.assertEqual(
            manifest[1]["requiredExecutedLcnfForms"], ["fap", "return"]
        )
        self.assertEqual(
            manifest[1]["requiredExecutedLcnfFormCounts"],
            [
                {"form": "fap", "minimum": 1, "maximum": 3},
                {"form": "return", "minimum": 2, "maximum": None},
            ],
        )
        self.assertEqual(
            manifest[1]["requiredExecutedLcnfFormTrace"],
            ["return", "fap", "return"],
        )
        self.assertEqual(
            manifest[1]["requiredAdministrativeStepKinds"],
            ["admin:invoke-name", "admin:yield-done"],
        )
        self.assertEqual(
            manifest[1]["requiredExternals"], ["ByteArray.size", "Nat.add"]
        )
        self.assertEqual(
            manifest[1]["requiredExecutedExternals"], ["ByteArray.size", "Nat.add"]
        )
        self.assertEqual(
            manifest[1]["requiredExecutedExternalCounts"],
            [
                {"external": "ByteArray.size", "minimum": 1, "maximum": 1},
                {"external": "Nat.add", "minimum": 2, "maximum": None},
            ],
        )
        self.assertEqual(
            manifest[1]["requiredExecutedExternalTrace"],
            ["Nat.add", "ByteArray.size", "Nat.add"],
        )
        self.assertEqual(
            [projection["external"] for projection in manifest[1]["effectProjections"]],
            ["ByteArray.size", "Nat.add"],
        )

    def test_executed_manifest_obligations_are_required_and_validated(self) -> None:
        malformed = descriptor("case")
        malformed["requiredExecutedLcnfForms"] = "return"
        with self.assertRaisesRegex(
            harness.ValidationError, "malformed requiredExecutedLcnfForms"
        ):
            harness.manifest_from_output(json.dumps(malformed), ["native", "--manifest"])

        duplicate = descriptor("case", executed_forms=["return", "return"])
        with self.assertRaisesRegex(
            harness.ValidationError, "duplicate requiredExecutedLcnfForms"
        ):
            harness.manifest_from_output(json.dumps(duplicate), ["native", "--manifest"])

        missing = descriptor("case")
        del missing["requiredExecutedLcnfForms"]
        with self.assertRaisesRegex(
            harness.ValidationError, "missing requiredExecutedLcnfForms"
        ):
            harness.manifest_from_output(json.dumps(missing), ["native", "--manifest"])

        missing_counts = descriptor("case")
        del missing_counts["requiredExecutedLcnfFormCounts"]
        with self.assertRaisesRegex(
            harness.ValidationError, "missing requiredExecutedLcnfFormCounts"
        ):
            harness.manifest_from_output(
                json.dumps(missing_counts), ["native", "--manifest"]
            )

        missing_trace = descriptor("case")
        del missing_trace["requiredExecutedLcnfFormTrace"]
        with self.assertRaisesRegex(
            harness.ValidationError, "missing requiredExecutedLcnfFormTrace"
        ):
            harness.manifest_from_output(
                json.dumps(missing_trace), ["native", "--manifest"]
            )

        for malformed_trace in ("cases,return", ["cases", ""], ["cases", 1]):
            malformed = descriptor("case")
            malformed["requiredExecutedLcnfFormTrace"] = malformed_trace
            with self.subTest(malformed_trace=malformed_trace):
                with self.assertRaisesRegex(
                    harness.ValidationError,
                    "malformed requiredExecutedLcnfFormTrace",
                ):
                    harness.manifest_from_output(
                        json.dumps(malformed), ["native", "--manifest"]
                    )

        missing_step_kinds = descriptor("case")
        del missing_step_kinds["requiredAdministrativeStepKinds"]
        with self.assertRaisesRegex(
            harness.ValidationError, "missing requiredAdministrativeStepKinds"
        ):
            harness.manifest_from_output(
                json.dumps(missing_step_kinds), ["native", "--manifest"]
            )

        for malformed_step_kinds in (
            "admin:invoke-name",
            ["admin:invoke-name", ""],
            ["admin:invoke-name", 1],
        ):
            malformed = descriptor("case")
            malformed["requiredAdministrativeStepKinds"] = (
                malformed_step_kinds
            )
            with self.subTest(malformed_step_kinds=malformed_step_kinds):
                with self.assertRaisesRegex(
                    harness.ValidationError,
                    "malformed requiredAdministrativeStepKinds",
                ):
                    harness.manifest_from_output(
                        json.dumps(malformed), ["native", "--manifest"]
                    )

        duplicate_step_kinds = descriptor(
            "case",
            required_administrative_step_kinds=[
                "admin:invoke-name",
                "admin:invoke-name",
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError, "duplicate requiredAdministrativeStepKinds"
        ):
            harness.manifest_from_output(
                json.dumps(duplicate_step_kinds), ["native", "--manifest"]
            )

        unknown_step_kind = descriptor(
            "case",
            required_administrative_step_kinds=["admin:not-a-step"],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "unknown requiredAdministrativeStepKinds: admin:not-a-step",
        ):
            harness.manifest_from_output(
                json.dumps(unknown_step_kind), ["native", "--manifest"]
            )

        for malformed_counts in (
            "oset=2",
            [{"form": "oset", "minimum": 2}],
            [{"form": "oset", "minimum": 0, "maximum": None}],
            [{"form": "oset", "minimum": 0, "maximum": 1}],
            [{"form": "oset", "minimum": -1, "maximum": 0}],
            [{"form": "oset", "minimum": True, "maximum": None}],
            [{"form": "", "minimum": 2, "maximum": None}],
            [{"form": "oset", "minimum": 2, "maximum": 1}],
            [{"form": "oset", "minimum": 2, "maximum": True}],
            [{"form": "oset", "minimum": 2, "maximum": "3"}],
            [{"form": "oset", "minimum": 2, "maximum": None, "extra": 1}],
        ):
            malformed = descriptor("case", executed_forms=["oset"])
            malformed["requiredExecutedLcnfFormCounts"] = malformed_counts
            with self.subTest(malformed_counts=malformed_counts):
                with self.assertRaisesRegex(
                    harness.ValidationError,
                    "malformed requiredExecutedLcnfFormCounts",
                ):
                    harness.manifest_from_output(
                        json.dumps(malformed), ["native", "--manifest"]
                    )

        duplicate_counts = descriptor(
            "case",
            executed_forms=["oset"],
            executed_form_counts=[
                {"form": "oset", "minimum": 1, "maximum": None},
                {"form": "oset", "minimum": 2, "maximum": None},
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError, "duplicate requiredExecutedLcnfFormCounts"
        ):
            harness.manifest_from_output(
                json.dumps(duplicate_counts), ["native", "--manifest"]
            )

        unrequired_count = descriptor(
            "case",
            executed_forms=["return"],
            executed_form_counts=[
                {"form": "oset", "minimum": 2, "maximum": None}
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError, "counted executed LCNF forms must also be required"
        ):
            harness.manifest_from_output(
                json.dumps(unrequired_count), ["native", "--manifest"]
            )

        zero_count = descriptor(
            "case",
            forms=["oset", "return"],
            executed_forms=["return"],
            executed_form_counts=[
                {"form": "oset", "minimum": 0, "maximum": 0}
            ],
        )
        prepared = harness.manifest_from_output(
            json.dumps(zero_count), ["native", "--manifest"]
        )
        self.assertEqual(
            prepared[0]["requiredExecutedLcnfFormCounts"],
            [{"form": "oset", "minimum": 0, "maximum": 0}],
        )

        zero_not_static = descriptor(
            "case",
            executed_forms=["return"],
            executed_form_counts=[
                {"form": "oset", "minimum": 0, "maximum": 0}
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "zero-counted LCNF forms must also be statically required",
        ):
            harness.manifest_from_output(
                json.dumps(zero_not_static), ["native", "--manifest"]
            )

        zero_required_executed = descriptor(
            "case",
            forms=["oset", "return"],
            executed_forms=["oset", "return"],
            executed_form_counts=[
                {"form": "oset", "minimum": 0, "maximum": 0}
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "zero-counted LCNF forms cannot also be required executed",
        ):
            harness.manifest_from_output(
                json.dumps(zero_required_executed), ["native", "--manifest"]
            )

        trace_missing_required_form = descriptor(
            "case",
            executed_forms=["cases", "return"],
            required_executed_form_trace=["return"],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "must contain every requiredExecutedLcnfForms name",
        ):
            harness.manifest_from_output(
                json.dumps(trace_missing_required_form), ["native", "--manifest"]
            )

        trace_violates_counts = descriptor(
            "case",
            executed_forms=["cases", "return"],
            executed_form_counts=[
                {"form": "cases", "minimum": 2, "maximum": 2}
            ],
            required_executed_form_trace=["cases", "return"],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "violates requiredExecutedLcnfFormCounts",
        ):
            harness.manifest_from_output(
                json.dumps(trace_violates_counts), ["native", "--manifest"]
            )

    def test_duplicate_manifest_id_rejected(self) -> None:
        line = json.dumps(descriptor("case"))
        with self.assertRaisesRegex(harness.ValidationError, "duplicate case IDs"):
            harness.manifest_from_output(f"{line}\n{line}\n", ["native", "--manifest"])

    def test_external_manifest_obligations_are_required_and_validated(self) -> None:
        for field in ("requiredExternals", "requiredExecutedExternals"):
            with self.subTest(field=field, problem="missing"):
                item = descriptor("case")
                del item[field]
                with self.assertRaisesRegex(harness.ValidationError, f"missing {field}"):
                    harness.manifest_from_output(
                        json.dumps(item), ["native", "--manifest"]
                    )

            with self.subTest(field=field, problem="malformed"):
                item = descriptor("case")
                item[field] = "Nat.add"
                with self.assertRaisesRegex(
                    harness.ValidationError, f"malformed {field}"
                ):
                    harness.manifest_from_output(
                        json.dumps(item), ["native", "--manifest"]
                    )

            with self.subTest(field=field, problem="duplicate"):
                item = descriptor("case")
                item[field] = ["Nat.add", "Nat.add"]
                with self.assertRaisesRegex(
                    harness.ValidationError, f"duplicate {field}"
                ):
                    harness.manifest_from_output(
                        json.dumps(item), ["native", "--manifest"]
                    )

        missing_counts = descriptor("case")
        del missing_counts["requiredExecutedExternalCounts"]
        with self.assertRaisesRegex(
            harness.ValidationError, "missing requiredExecutedExternalCounts"
        ):
            harness.manifest_from_output(
                json.dumps(missing_counts), ["native", "--manifest"]
            )

        missing_trace = descriptor("case")
        del missing_trace["requiredExecutedExternalTrace"]
        with self.assertRaisesRegex(
            harness.ValidationError, "missing requiredExecutedExternalTrace"
        ):
            harness.manifest_from_output(
                json.dumps(missing_trace), ["native", "--manifest"]
            )

        for malformed_trace in ("Nat.add", ["Nat.add", ""], ["Nat.add", 1]):
            malformed = descriptor("case")
            malformed["requiredExecutedExternalTrace"] = malformed_trace
            with self.subTest(malformed_trace=malformed_trace):
                with self.assertRaisesRegex(
                    harness.ValidationError,
                    "malformed requiredExecutedExternalTrace",
                ):
                    harness.manifest_from_output(
                        json.dumps(malformed), ["native", "--manifest"]
                    )

        for malformed_counts in (
            "Nat.add=2",
            [{"external": "Nat.add", "minimum": 2}],
            [{"external": "Nat.add", "minimum": 0, "maximum": None}],
            [{"external": "Nat.add", "minimum": 0, "maximum": 1}],
            [{"external": "Nat.add", "minimum": -1, "maximum": 0}],
            [{"external": "Nat.add", "minimum": True, "maximum": None}],
            [{"external": "", "minimum": 2, "maximum": None}],
            [{"external": "Nat.add", "minimum": 2, "maximum": 1}],
            [{"external": "Nat.add", "minimum": 2, "maximum": True}],
            [{"external": "Nat.add", "minimum": 2, "maximum": "3"}],
            [
                {
                    "external": "Nat.add",
                    "minimum": 2,
                    "maximum": None,
                    "extra": 1,
                }
            ],
        ):
            malformed = descriptor("case", executed_externals=["Nat.add"])
            malformed["requiredExecutedExternalCounts"] = malformed_counts
            with self.subTest(malformed_counts=malformed_counts):
                with self.assertRaisesRegex(
                    harness.ValidationError,
                    "malformed requiredExecutedExternalCounts",
                ):
                    harness.manifest_from_output(
                        json.dumps(malformed), ["native", "--manifest"]
                    )

        duplicate_counts = descriptor(
            "case",
            executed_externals=["Nat.add"],
            executed_external_counts=[
                {"external": "Nat.add", "minimum": 1, "maximum": None},
                {"external": "Nat.add", "minimum": 2, "maximum": None},
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError, "duplicate requiredExecutedExternalCounts"
        ):
            harness.manifest_from_output(
                json.dumps(duplicate_counts), ["native", "--manifest"]
            )

        unrequired_count = descriptor(
            "case",
            executed_externals=["Nat.add"],
            executed_external_counts=[
                {"external": "ByteArray.size", "minimum": 2, "maximum": None}
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError, "counted executed externals must also be required"
        ):
            harness.manifest_from_output(
                json.dumps(unrequired_count), ["native", "--manifest"]
            )

        zero_count = descriptor(
            "case",
            externals=["Nat.add"],
            executed_external_counts=[
                {"external": "Nat.add", "minimum": 0, "maximum": 0}
            ],
        )
        prepared = harness.manifest_from_output(
            json.dumps(zero_count), ["native", "--manifest"]
        )
        self.assertEqual(
            prepared[0]["requiredExecutedExternalCounts"],
            [{"external": "Nat.add", "minimum": 0, "maximum": 0}],
        )

        zero_not_static = descriptor(
            "case",
            executed_external_counts=[
                {"external": "Nat.add", "minimum": 0, "maximum": 0}
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "zero-counted externals must also be statically required",
        ):
            harness.manifest_from_output(
                json.dumps(zero_not_static), ["native", "--manifest"]
            )

        zero_required_executed = descriptor(
            "case",
            externals=["Nat.add"],
            executed_externals=["Nat.add"],
            executed_external_counts=[
                {"external": "Nat.add", "minimum": 0, "maximum": 0}
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "zero-counted externals cannot also be required executed",
        ):
            harness.manifest_from_output(
                json.dumps(zero_required_executed), ["native", "--manifest"]
            )

        wrong_trace_names = descriptor(
            "case",
            externals=["ByteArray.size", "Nat.add"],
            executed_externals=["Nat.add"],
            required_executed_external_trace=["ByteArray.size"],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "names must exactly match requiredExecutedExternals",
        ):
            harness.manifest_from_output(
                json.dumps(wrong_trace_names), ["native", "--manifest"]
            )

        trace_violates_counts = descriptor(
            "case",
            externals=["Nat.add"],
            executed_externals=["Nat.add"],
            executed_external_counts=[
                {"external": "Nat.add", "minimum": 2, "maximum": 2}
            ],
            required_executed_external_trace=["Nat.add"],
        )
        with self.assertRaisesRegex(
            harness.ValidationError,
            "violates requiredExecutedExternalCounts",
        ):
            harness.manifest_from_output(
                json.dumps(trace_violates_counts), ["native", "--manifest"]
            )

        exact_zero_trace = descriptor(
            "case",
            externals=["Nat.add"],
            executed_external_counts=[
                {"external": "Nat.add", "minimum": 0, "maximum": 0}
            ],
            required_executed_external_trace=[],
        )
        prepared = harness.manifest_from_output(
            json.dumps(exact_zero_trace), ["native", "--manifest"]
        )
        self.assertEqual(prepared[0]["requiredExecutedExternalTrace"], [])

    def test_effect_projections_are_required_and_validated(self) -> None:
        missing = descriptor("case")
        del missing["effectProjections"]
        with self.assertRaisesRegex(
            harness.ValidationError, "missing effectProjections"
        ):
            harness.manifest_from_output(json.dumps(missing), ["native", "--manifest"])

        malformed = descriptor("case")
        malformed["effectProjections"] = "Effect.record"
        with self.assertRaisesRegex(
            harness.ValidationError, "malformed effectProjections"
        ):
            harness.manifest_from_output(json.dumps(malformed), ["native", "--manifest"])

        incomplete = descriptor("case")
        incomplete["effectProjections"] = [
            {
                "external": "Effect.record",
                "operation": "validation.record",
                "argSchemas": ["nat"],
            }
        ]
        with self.assertRaisesRegex(
            harness.ValidationError, "malformed effectProjections"
        ):
            harness.manifest_from_output(json.dumps(incomplete), ["native", "--manifest"])

        duplicate = descriptor("case")
        duplicate["effectProjections"] = [
            {
                "external": "Effect.record",
                "operation": operation,
                "argSchemas": ["nat"],
                "resultSchema": "nat",
            }
            for operation in ("validation.first", "validation.second")
        ]
        with self.assertRaisesRegex(
            harness.ValidationError, "duplicate effectProjections"
        ):
            harness.manifest_from_output(json.dumps(duplicate), ["native", "--manifest"])

        unexecuted = descriptor(
            "case",
            externals=["Effect.record"],
            effect_projections=[
                {
                    "external": "Effect.record",
                    "operation": "validation.record",
                    "argSchemas": ["nat"],
                    "resultSchema": "nat",
                }
            ],
        )
        with self.assertRaisesRegex(
            harness.ValidationError, "must be required and executed"
        ):
            harness.manifest_from_output(json.dumps(unexecuted), ["native", "--manifest"])

    def test_malformed_manifest_descriptor_rejected(self) -> None:
        item = descriptor("case")
        del item["provenance"]
        with self.assertRaisesRegex(harness.ValidationError, "missing provenance"):
            harness.manifest_from_output(json.dumps(item), ["native", "--manifest"])

    def test_manifest_protocol_version_rejected(self) -> None:
        item = descriptor("case")
        item["version"] = 4
        with self.assertRaisesRegex(harness.ValidationError, "protocol version 4"):
            harness.manifest_from_output(json.dumps(item), ["native", "--manifest"])

    def test_manifest_argument_arity_rejected(self) -> None:
        item = descriptor("case")
        item["argSchemas"] = []
        with self.assertRaisesRegex(harness.ValidationError, "argument arity mismatch"):
            harness.manifest_from_output(json.dumps(item), ["native", "--manifest"])

    def test_manifest_argument_alias_contract_rejected(self) -> None:
        base = descriptor("case")
        base["args"] = [
            {"bytes": {"value": [1]}},
            {"bytes": {"value": [1]}},
            {"bytes": {"value": [1]}},
        ]
        base["argSchemas"] = ["bytes", "bytes", "bytes"]
        malformed = [
            ("malformed", [{"source": 0}]),
            ("canonical bounds", [{"source": 1, "target": 1}]),
            (
                "strictly increasing",
                [{"source": 0, "target": 2}, {"source": 0, "target": 1}],
            ),
            (
                "independently materialized root",
                [{"source": 0, "target": 1}, {"source": 1, "target": 2}],
            ),
        ]
        for message, aliases in malformed:
            with self.subTest(message=message):
                item = dict(base)
                item["argumentAliases"] = aliases
                with self.assertRaisesRegex(harness.ValidationError, message):
                    harness.manifest_from_output(
                        json.dumps(item), ["native", "--manifest"]
                    )

        schema_mismatch = dict(base)
        schema_mismatch["argSchemas"] = ["bytes", "string", "bytes"]
        schema_mismatch["argumentAliases"] = [{"source": 0, "target": 1}]
        with self.assertRaisesRegex(harness.ValidationError, "different schemas"):
            harness.manifest_from_output(
                json.dumps(schema_mismatch), ["native", "--manifest"]
            )

        fixture_mismatch = dict(base)
        fixture_mismatch["args"] = list(base["args"])
        fixture_mismatch["args"][1] = {"bytes": {"value": [2]}}
        fixture_mismatch["argumentAliases"] = [{"source": 0, "target": 1}]
        with self.assertRaisesRegex(harness.ValidationError, "different fixtures"):
            harness.manifest_from_output(
                json.dumps(fixture_mismatch), ["native", "--manifest"]
            )

    def test_manifest_argument_alias_stars_and_independent_roots_accepted(self) -> None:
        item = descriptor("case")
        item["args"] = [
            {"bytes": {"value": [1]}},
            {"bytes": {"value": [1]}},
            {"bytes": {"value": [1]}},
            {"bytes": {"value": [2]}},
            {"bytes": {"value": [2]}},
        ]
        item["argSchemas"] = ["bytes", "bytes", "bytes", "bytes", "bytes"]
        item["argumentAliases"] = [
            {"source": 0, "target": 1},
            {"source": 0, "target": 2},
            {"source": 3, "target": 4},
        ]
        prepared = harness.manifest_from_output(
            json.dumps(item), ["native", "--manifest"]
        )
        self.assertEqual(prepared[0]["argumentAliases"], item["argumentAliases"])

    def test_manifest_nested_argument_alias_contract(self) -> None:
        item = descriptor("nested-alias")
        byte_value = {"bytes": {"value": [1, 2, 3]}}
        item["args"] = [{
            "ctor": {
                "name": "NestedAliasInput",
                "tag": 0,
                "fields": [byte_value, byte_value],
            }
        }]
        item["argSchemas"] = [{
            "ctor": {
                "name": "NestedAliasInput",
                "tag": 0,
                "fields": ["bytes", "bytes"],
            }
        }]
        item["nestedArgumentAliases"] = [{
            "source": {"argument": 0, "children": [0]},
            "target": {"argument": 0, "children": [1]},
        }]
        prepared = harness.manifest_from_output(
            json.dumps(item), ["native", "--manifest"]
        )
        self.assertEqual(
            prepared[0]["nestedArgumentAliases"], item["nestedArgumentAliases"]
        )

        empty_path = dict(item)
        empty_path["nestedArgumentAliases"] = [{
            "source": {"argument": 0, "children": []},
            "target": {"argument": 0, "children": [1]},
        }]
        with self.assertRaisesRegex(harness.ValidationError, "malformed nested argument path"):
            harness.manifest_from_output(
                json.dumps(empty_path), ["native", "--manifest"]
            )

        reversed_path = dict(item)
        reversed_path["nestedArgumentAliases"] = [{
            "source": {"argument": 0, "children": [1]},
            "target": {"argument": 0, "children": [0]},
        }]
        with self.assertRaisesRegex(harness.ValidationError, "must precede target"):
            harness.manifest_from_output(
                json.dumps(reversed_path), ["native", "--manifest"]
            )

        fixture_mismatch = json.loads(json.dumps(item))
        fixture_mismatch["args"][0]["ctor"]["fields"][1] = {
            "bytes": {"value": [9]}
        }
        with self.assertRaisesRegex(harness.ValidationError, "different fixtures"):
            harness.manifest_from_output(
                json.dumps(fixture_mismatch), ["native", "--manifest"]
            )

        below_root_alias = json.loads(json.dumps(item))
        below_root_alias["args"].append(below_root_alias["args"][0])
        below_root_alias["argSchemas"].append(below_root_alias["argSchemas"][0])
        below_root_alias["argumentAliases"] = [{"source": 0, "target": 1}]
        below_root_alias["nestedArgumentAliases"][0]["target"]["argument"] = 1
        with self.assertRaisesRegex(harness.ValidationError, "top-level alias target"):
            harness.manifest_from_output(
                json.dumps(below_root_alias), ["native", "--manifest"]
            )

    def test_manifest_drives_tag_and_explicit_selection(self) -> None:
        manifest = [
            descriptor("a-case", tags=["quick"]),
            descriptor("b-case", tags=["extended"]),
            descriptor(
                "c-case", tags=["quick", "wasm-generation-pending"]
            ),
        ]
        self.assertEqual(
            harness.select_cases(manifest, None, "quick"),
            ["a-case", "c-case"],
        )
        self.assertEqual(harness.select_cases(manifest, ["b-case"], "quick"), ["b-case"])
        self.assertEqual(
            harness.select_cases(
                manifest, None, None, ("wasm-generation-pending",)
            ),
            ["a-case", "b-case"],
        )
        self.assertEqual(
            harness.select_cases(
                manifest, None, "quick", ("wasm-generation-pending",)
            ),
            ["a-case"],
        )
        with self.assertRaisesRegex(
            harness.ValidationError, "excluded by plan tag"
        ):
            harness.select_cases(
                manifest,
                ["c-case"],
                None,
                ("wasm-generation-pending",),
            )
        with self.assertRaisesRegex(harness.ValidationError, "selected no cases"):
            harness.select_cases(manifest, None, "missing")
        with self.assertRaisesRegex(harness.ValidationError, "selected no cases"):
            harness.select_cases(
                [manifest[2]], None, None, ("wasm-generation-pending",)
            )

    def test_corpus_artifact_is_deterministic(self) -> None:
        manifest = [descriptor("a-case", tags=["quick", "data"])]
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            harness.write_corpus_manifest(out_dir, manifest)
            first = (out_dir / "corpus.json").read_bytes()
            harness.write_corpus_manifest(out_dir, manifest)
            self.assertEqual(first, (out_dir / "corpus.json").read_bytes())
            artifact = json.loads(first)
            self.assertEqual(artifact, {"version": 3, "cases": manifest})

    def test_evidence_blobs_are_append_only_and_content_addressed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            content = b"retained evidence\0"
            digest = harness.sha256_bytes(content)
            relative = harness.retain_evidence_blob(
                out_dir, "inputs", digest, content
            )
            self.assertEqual(relative, f"evidence/inputs/{digest}")
            self.assertEqual((out_dir / relative).read_bytes(), content)
            self.assertEqual(
                harness.retain_evidence_blob(
                    out_dir, "inputs", digest, content
                ),
                relative,
            )

            (out_dir / relative).write_bytes(b"corrupt")
            with self.assertRaisesRegex(
                harness.ValidationError, "disagrees with SHA-256"
            ):
                harness.retain_evidence_blob(
                    out_dir, "inputs", digest, content
                )

            (out_dir / "evidence" / "inputs").rename(
                out_dir / "real-inputs"
            )
            (out_dir / "evidence" / "inputs").symlink_to(
                out_dir / "real-inputs", target_is_directory=True
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "directory contains a symlink"
            ):
                harness.retain_evidence_blob(
                    out_dir, "inputs", harness.sha256_bytes(b"other"), b"other"
                )

    def test_evidence_comparison_preserves_order_and_multiplicity(self) -> None:
        ordered = core.ordered_evidence_delta(["a", "b"], ["b", "a"])
        self.assertTrue(ordered["changed"])
        self.assertTrue(ordered["orderChanged"])
        self.assertEqual(ordered["added"], [])
        self.assertEqual(ordered["removed"], [])

        first = {"phase": "comparison", "message": "first"}
        second = {"phase": "comparison", "message": "second"}
        findings = core.evidence_findings_delta(
            [first, first], [first, second]
        )
        self.assertEqual(
            findings,
            {
                "added": [{"finding": second, "count": 1}],
                "removed": [{"finding": first, "count": 1}],
            },
        )

        with mock.patch.object(
            sys, "argv", ["validate_interpreters.py", "--json"]
        ):
            with self.assertRaisesRegex(
                harness.ValidationError,
                "--json requires --compare-evidence",
            ):
                harness.main()

    def test_backend_artifact_inventory_is_sorted_and_content_addressed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            descriptors = [descriptor("case")]
            context = harness.RunContext(
                harness.ROOT, out_dir, descriptors, ["case"]
            )
            harness.write_corpus_manifest(out_dir, descriptors)
            result = harness.write_artifact(
                out_dir, "case", "v8", success("case", "v8")
            )
            process = harness.write_process_artifacts(
                out_dir / "v8",
                mock.Mock(stdout="", stderr="", returncode=0),
                "v8",
            )
            artifacts = (result, *process)
            harness.write_matrix_artifact(
                context,
                ["v8"],
                [],
                [],
                artifacts=tuple(reversed(artifacts)),
            )
            matrix_path = out_dir / "matrix.json"
            first = matrix_path.read_bytes()
            matrix = json.loads(first)
            first_manifest_path = harness.validation_evidence_manifest_path(
                out_dir,
                matrix["identity"]["run"],
                harness.sha256_bytes(first),
            )
            first_manifest_bytes = first_manifest_path.read_bytes()
            first_manifest = json.loads(first_manifest_bytes)
            self.assertEqual(
                first_manifest["matrix"],
                {
                    "sha256": harness.sha256_bytes(first),
                    "artifact": "evidence/matrices/"
                    + harness.sha256_bytes(first),
                },
            )
            self.assertEqual(
                (
                    out_dir / first_manifest["matrix"]["artifact"]
                ).read_bytes(),
                first,
            )
            self.assertEqual(
                [(item["kind"], item["name"]) for item in matrix["artifacts"]],
                [
                    ("backend-result", "case/v8/result.json"),
                    ("process-stderr", "v8/stderr.log"),
                    ("process-stdout", "v8/stdout.jsonl"),
                ],
            )
            self.assertEqual(matrix["summary"]["artifactCount"], 3)
            self.assertEqual(process[0].sha256, process[1].sha256)
            self.assertEqual(
                matrix["artifacts"][1]["artifact"],
                matrix["artifacts"][2]["artifact"],
            )
            harness.write_matrix_artifact(
                context,
                ["v8"],
                [],
                [],
                artifacts=artifacts,
            )
            self.assertEqual(first, matrix_path.read_bytes())
            self.assertEqual(first_manifest_bytes, first_manifest_path.read_bytes())
            self.assertEqual(
                list(first_manifest_path.parent.glob("*.json")),
                [first_manifest_path],
            )

            changed_process = harness.write_process_artifacts(
                out_dir / "v8",
                mock.Mock(
                    stdout="engine chatter\n",
                    stderr="diagnostic\n",
                    returncode=0,
                ),
                "v8",
            )
            harness.write_matrix_artifact(
                context,
                ["v8"],
                [],
                [],
                artifacts=(result, *changed_process),
            )
            changed_matrix = json.loads(matrix_path.read_bytes())
            changed_manifest_path = harness.validation_evidence_manifest_path(
                out_dir,
                changed_matrix["identity"]["run"],
                harness.sha256_bytes(matrix_path.read_bytes()),
            )
            self.assertEqual(
                matrix["identity"]["run"], changed_matrix["identity"]["run"]
            )
            self.assertNotEqual(
                matrix["artifacts"], changed_matrix["artifacts"]
            )
            self.assertNotEqual(first_manifest_path, changed_manifest_path)
            self.assertEqual(first_manifest_bytes, first_manifest_path.read_bytes())
            self.assertEqual(
                set(first_manifest_path.parent.glob("*.json")),
                {first_manifest_path, changed_manifest_path},
            )

            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate artifacts"
            ):
                harness.write_matrix_artifact(
                    context,
                    ["v8"],
                    [],
                    [],
                    artifacts=(result, result),
                )
            with self.assertRaisesRegex(
                harness.ValidationError, "inactive backend"
            ):
                harness.write_matrix_artifact(
                    context,
                    ["v8"],
                    [],
                    [],
                    artifacts=(
                        harness.ValidationArtifact(
                            "backend-result",
                            "case/talos/result.json",
                            result.sha256,
                            result.content,
                        ),
                    ),
                )

            first_manifest_path.write_bytes(b"corrupt bundle")
            with self.assertRaisesRegex(
                harness.ValidationError, "bundle disagrees with its identity"
            ):
                harness.write_matrix_artifact(
                    context,
                    ["v8"],
                    [],
                    [],
                    artifacts=artifacts,
                )
            self.assertEqual(first_manifest_path.read_bytes(), b"corrupt bundle")

    def test_comparison_artifact_names_actual_backends_and_is_deterministic(self) -> None:
        comparisons = [
            {
                "caseId": "case",
                "reference": "native",
                "candidate": "v8",
                "equal": True,
                "case": descriptor("case"),
            }
        ]
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            harness.write_comparison_artifact(
                out_dir, "native", "v8", comparisons
            )
            path = out_dir / "comparisons" / "native--v8.json"
            first = path.read_bytes()
            harness.write_comparison_artifact(
                out_dir, "native", "v8", comparisons
            )
            self.assertEqual(first, path.read_bytes())
            artifact = json.loads(first)
            self.assertEqual(artifact["reference"], "native")
            self.assertEqual(artifact["candidate"], "v8")
            self.assertEqual(artifact["comparisons"], comparisons)

    def test_comparison_artifact_rejects_unsafe_backend_names(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(
                harness.ValidationError, "candidate backend: name"
            ):
                harness.write_comparison_artifact(
                    Path(directory), "native", "../v8", []
                )

    def test_adapter_audit_and_semantic_mismatch_are_both_reported(self) -> None:
        class FakeAdapter:
            def __init__(
                self, name: str, record: dict, audit_failures: list[str] | None = None
            ) -> None:
                self.name = name
                self.record = record
                self.audit_failures = audit_failures or []

            def build(self, context: harness.BuildContext) -> None:
                pass

            def execute(self, context: harness.RunContext) -> harness.BackendRun:
                return harness.BackendRun(
                    self.name,
                    list(context.selected),
                    {self.record["caseId"]: self.record},
                )

            def audit(
                self,
                context: harness.RunContext,
                backend_run: harness.BackendRun,
            ) -> harness.BackendAudit:
                return harness.BackendAudit(
                    {"backend": self.name},
                    [
                        harness.ValidationFinding(
                            "audit", message, self.name, "case"
                        )
                        for message in self.audit_failures
                    ],
                )

        with tempfile.TemporaryDirectory() as directory:
            context = harness.RunContext(
                harness.ROOT,
                Path(directory),
                [descriptor("case")],
                ["case"],
            )
            reference = FakeAdapter("native", success("case", "native", 41))
            candidate = FakeAdapter(
                "v8",
                success("case", "v8", 42),
                ["case: candidate audit failed"],
            )
            comparisons, findings = harness.validate_pair(
                context, reference, candidate
            )
            self.assertFalse(comparisons[0]["equal"])
            self.assertEqual(len(findings), 2)
            self.assertIn("candidate audit failed", findings[0].message)
            self.assertIn("semantic mismatch", findings[1].message)
            self.assertTrue(
                (Path(directory) / "case" / "native" / "result.json").is_file()
            )
            self.assertTrue(
                (Path(directory) / "case" / "v8" / "result.json").is_file()
            )
            artifact = json.loads(
                (
                    Path(directory)
                    / "comparisons"
                    / "native--v8.json"
                ).read_text(encoding="utf-8")
            )
            self.assertEqual(
                [finding["phase"] for finding in artifact["findings"]],
                ["audit", "comparison"],
            )
            self.assertEqual(
                artifact["summary"],
                {
                    "selectedCases": 1,
                    "comparedCases": 1,
                    "equalCases": 0,
                    "findingCount": 2,
                },
            )

    def test_validation_matrix_executes_and_audits_each_backend_once(self) -> None:
        class CountingAdapter:
            def __init__(self, name: str) -> None:
                self.name = name
                self.execute_count = 0
                self.audit_count = 0

            def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
                return descriptors

            def build(self, context: harness.BuildContext) -> None:
                pass

            def execute(self, context: harness.RunContext) -> harness.BackendRun:
                self.execute_count += 1
                return harness.BackendRun(
                    self.name,
                    list(context.selected),
                    {"case": success("case", self.name)},
                )

            def audit(
                self,
                context: harness.RunContext,
                backend_run: harness.BackendRun,
            ) -> harness.BackendAudit:
                self.audit_count += 1
                return harness.BackendAudit()

        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            context = harness.RunContext(
                harness.ROOT, out_dir, [descriptor("case")], ["case"]
            )
            native = CountingAdapter("native")
            lcnf_adapter = CountingAdapter("lcnf")
            v8 = CountingAdapter("v8")
            talos = CountingAdapter("talos")
            pair_results, findings = harness.validate_matrix(
                context,
                [
                    (native, lcnf_adapter),
                    (native, v8),
                    (v8, talos),
                ],
            )
            self.assertEqual(findings, [])
            self.assertEqual(
                [
                    (result.reference, result.candidate)
                    for result in pair_results
                ],
                [("native", "lcnf"), ("native", "v8"), ("v8", "talos")],
            )
            for adapter in (native, lcnf_adapter, v8, talos):
                self.assertEqual(adapter.execute_count, 1)
                self.assertEqual(adapter.audit_count, 1)
                self.assertTrue(
                    (out_dir / "case" / adapter.name / "result.json").is_file()
                )
            for reference, candidate in (
                ("native", "lcnf"),
                ("native", "v8"),
                ("v8", "talos"),
            ):
                self.assertTrue(
                    (
                        out_dir
                        / "comparisons"
                        / f"{reference}--{candidate}.json"
                    ).is_file()
                )
            matrix_path = out_dir / "matrix.json"
            matrix_bytes = matrix_path.read_bytes()
            matrix = json.loads(matrix_bytes)
            self.assertEqual(
                matrix["backends"], ["native", "lcnf", "v8", "talos"]
            )
            self.assertEqual(
                [pair["artifact"].split("/")[:2] for pair in matrix["pairs"]],
                [["evidence", "comparisons"]] * 3,
            )
            for pair in matrix["pairs"]:
                self.assertTrue((out_dir / pair["artifact"]).is_file())
            self.assertEqual(
                matrix["summary"],
                {
                    "selectedCaseCount": 1,
                    "backendCount": 4,
                    "pairCount": 3,
                    "comparisonCount": 3,
                    "equalComparisonCount": 3,
                    "findingCount": 0,
                    "inputCount": 1,
                    "productCount": 0,
                    "toolCount": 0,
                    "buildInputCount": 0,
                    "artifactCount": 4,
                },
            )
            self.assertEqual(
                matrix["inputs"],
                [
                    {
                        "kind": "corpus",
                        "name": "corpus.json",
                        "sha256": harness.sha256_bytes(
                            harness.corpus_artifact_bytes(context.descriptors)
                        ),
                        "artifact": "evidence/inputs/"
                        + harness.sha256_bytes(
                            harness.corpus_artifact_bytes(context.descriptors)
                        ),
                    }
                ],
            )
            corpus_sha256 = matrix["inputs"][0]["sha256"]
            selection_sha256 = harness.validation_selection_sha256(
                corpus_sha256, ["case"]
            )
            self.assertEqual(
                matrix["identity"],
                {
                    "algorithm": "sha256",
                    "selection": selection_sha256,
                    "run": harness.validation_run_sha256(
                        selection_sha256,
                        ["native", "lcnf", "v8", "talos"],
                        [
                            ("native", "lcnf"),
                            ("native", "v8"),
                            ("v8", "talos"),
                        ],
                        (
                            harness.ValidationInput(
                                "corpus", "corpus.json", corpus_sha256
                            ),
                        ),
                        [],
                    ),
                },
            )
            self.assertEqual(matrix["products"], [])
            self.assertEqual(matrix["tools"], [])
            self.assertEqual(
                [artifact["name"] for artifact in matrix["artifacts"]],
                [
                    "case/lcnf/result.json",
                    "case/native/result.json",
                    "case/talos/result.json",
                    "case/v8/result.json",
                ],
            )
            captured_artifacts = tuple(
                harness.ValidationArtifact(
                    artifact["kind"],
                    artifact["name"],
                    artifact["sha256"],
                    (out_dir / artifact["artifact"]).read_bytes(),
                )
                for artifact in matrix["artifacts"]
            )
            harness.write_matrix_artifact(
                context,
                ["native", "lcnf", "v8", "talos"],
                pair_results,
                findings,
                artifacts=captured_artifacts,
            )
            self.assertEqual(matrix_bytes, matrix_path.read_bytes())

            duplicate_input_context = harness.RunContext(
                context.root,
                context.out_dir,
                context.descriptors,
                context.selected,
                (
                    harness.ValidationInput("adapter-config", "v8.json", "0" * 64),
                    harness.ValidationInput("adapter-config", "v8.json", "1" * 64),
                ),
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate provenance inputs"
            ):
                harness.write_matrix_artifact(
                    duplicate_input_context,
                    ["native", "lcnf", "v8", "talos"],
                    pair_results,
                    findings,
                )

            with self.assertRaisesRegex(
                harness.ValidationError, "selected more than once"
            ):
                harness.validate_matrix(
                    context, [(native, v8), (native, v8)]
                )
            self.assertEqual(native.execute_count, 1)
            self.assertEqual(v8.execute_count, 1)

    def test_product_provider_is_built_once_for_two_consumers_and_verified_offline(
        self,
    ) -> None:
        contract = harness.ProductContract(
            "wasm", "wasm32", "fixture", "fixture-v1"
        )

        class CountingProvider:
            name = "fixture-wasm"

            def __init__(self) -> None:
                self.build_count = 0

            def build(
                self, context: harness.BuildContext
            ) -> harness.ProductProviderRun:
                self.build_count += 1
                self.assert_context(context)
                assert context.run_context is not None
                provider_dir = context.out_dir / self.name
                modules_dir = provider_dir / "modules"
                modules_dir.mkdir(parents=True)
                product_bytes = {
                    "first": b"\0asm\x01\0\0\0first",
                    "second": b"\0asm\x01\0\0\0second",
                }
                ordinary = []
                for case_id, content in product_bytes.items():
                    path = modules_dir / f"{case_id}.wasm"
                    path.write_bytes(content)
                    ordinary.append(
                        harness.ValidationProduct(
                            self.name,
                            "wasm-module",
                            f"modules/{case_id}.wasm",
                            harness.sha256_bytes(content),
                        )
                    )
                manifest_value = {
                    "version": 3,
                    "contract": contract.to_json(),
                    "products": [
                        {"kind": product.kind, "path": product.name}
                        for product in ordinary
                    ],
                    "cases": [
                        {
                            "caseId": case_id,
                            "products": [
                                {
                                    "kind": "wasm-module",
                                    "path": f"modules/{case_id}.wasm",
                                }
                            ],
                        }
                        for case_id in ("first", "second")
                    ],
                }
                manifest_content = (
                    json.dumps(manifest_value, indent=2, sort_keys=True) + "\n"
                ).encode("utf-8")
                manifest_path = provider_dir / "bundle.json"
                manifest_path.write_bytes(manifest_content)
                products = tuple(
                    sorted(
                        [
                            *ordinary,
                            harness.ValidationProduct(
                                self.name,
                                core.RESERVED_PRODUCT_KIND,
                                "bundle.json",
                                harness.sha256_bytes(manifest_content),
                            ),
                        ],
                        key=lambda product: (product.kind, product.name),
                    )
                )
                bundle = core.product_bundle_from_manifest(
                    self.name,
                    contract,
                    manifest_content,
                    products,
                    context.run_context.selected,
                    "fixture bundle",
                )
                return harness.ProductProviderRun(
                    self.name, bundle, products=list(products)
                )

            def assert_context(self, context: harness.BuildContext) -> None:
                if context.run_context is None:
                    raise AssertionError("provider received no run context")

        class CountingConsumer:
            def __init__(self, name: str) -> None:
                self.name = name
                self.product_provider = harness.ProductProviderRequirement(
                    "fixture-wasm", contract
                )
                self.execute_count = 0
                self.audit_count = 0

            def execute(
                self, context: harness.RunContext
            ) -> harness.BackendRun:
                self.execute_count += 1
                bundle = context.product_bundles["fixture-wasm"]
                results = {}
                for case_id in context.selected:
                    record = success(case_id, self.name)
                    record["diagnostics"] = [
                        {
                            "key": core.PRODUCT_BUNDLE_RECEIPT_DIAGNOSTIC,
                            "value": harness.product_bundle_receipt_value(
                                bundle, case_id
                            ),
                        }
                    ]
                    results[case_id] = record
                return harness.BackendRun(
                    self.name, list(context.selected), results=results
                )

            def audit(
                self,
                context: harness.RunContext,
                backend_run: harness.BackendRun,
            ) -> harness.BackendAudit:
                self.audit_count += 1
                return harness.BackendAudit()

        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            descriptors = [descriptor("first"), descriptor("second")]
            harness.write_corpus_manifest(out_dir, descriptors)
            control_inputs = (
                config_input(
                    "provider-config",
                    "provider.json",
                    fixture_provider_config("fixture-wasm", contract),
                ),
                config_input(
                    "adapter-config",
                    "v8.json",
                    fixture_consumer_config(
                        "v8", "fixture-wasm", contract
                    ),
                ),
                config_input(
                    "adapter-config",
                    "talos.json",
                    fixture_consumer_config(
                        "talos", "fixture-wasm", contract
                    ),
                ),
            )
            base_context = harness.RunContext(
                harness.ROOT,
                out_dir,
                descriptors,
                ["first", "second"],
                control_inputs,
            )
            provider = CountingProvider()
            provider_runs = harness.build_product_providers(
                harness.BuildContext(
                    harness.ROOT, out_dir, False, base_context
                ),
                (provider,),
            )
            context = harness.RunContext(
                base_context.root,
                base_context.out_dir,
                base_context.descriptors,
                base_context.selected,
                base_context.inputs,
                product_bundles={
                    run.provider: run.bundle for run in provider_runs
                },
            )
            v8 = CountingConsumer("v8")
            talos = CountingConsumer("talos")
            pair_results, findings = harness.validate_matrix(
                context, [(v8, talos)], provider_runs
            )
            self.assertEqual(provider.build_count, 1)
            self.assertEqual(findings, [])
            self.assertEqual(len(pair_results[0].comparisons), 2)
            self.assertTrue(
                all(item["equal"] for item in pair_results[0].comparisons)
            )
            for consumer in (v8, talos):
                self.assertEqual(consumer.execute_count, 1)
                self.assertEqual(consumer.audit_count, 1)

            matrix_path = out_dir / "matrix.json"
            matrix_content = matrix_path.read_bytes()
            matrix = json.loads(matrix_content)
            bundle_value = matrix["productBundles"][0]
            self.assertEqual(matrix["providers"], ["fixture-wasm"])
            self.assertEqual(
                [consumer["backend"] for consumer in matrix["productConsumers"]],
                ["talos", "v8"],
            )
            self.assertEqual(len(bundle_value["products"]), 2)
            self.assertEqual(matrix["summary"]["productCount"], 3)
            self.assertEqual(matrix["summary"]["providerCount"], 1)
            self.assertEqual(matrix["summary"]["bundleCount"], 1)
            self.assertEqual(matrix["summary"]["productConsumerCount"], 2)
            self.assertEqual(matrix["summary"]["productReceiptCount"], 4)
            self.assertEqual(
                matrix["coverage"],
                {
                    "selectedCaseCount": 2,
                    "expectedBackendResultCount": 4,
                    "backendResultCount": 4,
                    "successfulBackendResultCount": 4,
                    "findingCount": 0,
                    "unassignedFindingCount": 0,
                    "backends": [
                        {
                            "backend": "v8",
                            "selectedCaseCount": 2,
                            "resultCaseCount": 2,
                            "successfulCaseCount": 2,
                            "comparisonCount": 2,
                            "equalComparisonCount": 2,
                            "findingCount": 0,
                        },
                        {
                            "backend": "talos",
                            "selectedCaseCount": 2,
                            "resultCaseCount": 2,
                            "successfulCaseCount": 2,
                            "comparisonCount": 2,
                            "equalComparisonCount": 2,
                            "findingCount": 0,
                        },
                    ],
                    "pairs": [
                        {
                            "reference": "v8",
                            "candidate": "talos",
                            "selectedCaseCount": 2,
                            "comparedCaseCount": 2,
                            "equalCaseCount": 2,
                            "findingCount": 0,
                        }
                    ],
                    "providers": [
                        {
                            "provider": "fixture-wasm",
                            "bundleCaseCount": 2,
                            "bundleProductCount": 2,
                            "consumerCount": 2,
                            "findingCount": 0,
                        }
                    ],
                    "consumers": [
                        {
                            "backend": backend,
                            "provider": "fixture-wasm",
                            "selectedCaseCount": 2,
                            "receiptCaseCount": 2,
                            "receiptedProductReferenceCount": 2,
                            "uniqueReceiptedProductCount": 2,
                            "executionAccess": {
                                "recorded": False,
                                "recorder": None,
                                "openedReceiptedProductCount": 0,
                                "traceAccessCount": 0,
                            },
                        }
                        for backend in ("talos", "v8")
                    ],
                },
            )
            self.assertEqual(
                [
                    (receipt["backend"], receipt["caseId"])
                    for receipt in matrix["productReceipts"]
                ],
                [
                    ("talos", "first"),
                    ("talos", "second"),
                    ("v8", "first"),
                    ("v8", "second"),
                ],
            )
            bundle_digest = bundle_value["bundleSha256"]
            for backend in ("v8", "talos"):
                for case_id in ("first", "second"):
                    record = json.loads(
                        (
                            out_dir
                            / case_id
                            / backend
                            / "result.json"
                        ).read_text(encoding="utf-8")
                    )
                    receipt = json.loads(record["diagnostics"][0]["value"])
                    self.assertEqual(receipt["provider"], "fixture-wasm")
                    self.assertEqual(receipt["bundleSha256"], bundle_digest)
                    self.assertEqual(
                        [product["name"] for product in receipt["products"]],
                        [f"modules/{case_id}.wasm"],
                    )

            evidence_path = harness.validation_evidence_manifest_path(
                out_dir,
                matrix["identity"]["run"],
                harness.sha256_bytes(matrix_content),
            )
            shutil.rmtree(out_dir / "fixture-wasm")
            evidence = harness.verify_evidence_manifest(evidence_path)
            self.assertEqual(evidence["coverage"], matrix["coverage"])

            artifact = next(
                item for item in matrix["artifacts"]
                if item["kind"] == "backend-result"
                and item["name"] == "first/talos/result.json"
            )
            record = json.loads(
                (out_dir / artifact["artifact"]).read_text(encoding="utf-8")
            )
            wrong_product = bundle_value["cases"][1]["products"][0]
            record["diagnostics"][0]["value"] = json.dumps(
                {
                    "provider": "fixture-wasm",
                    "bundleSha256": bundle_digest,
                    "products": [
                        {
                            "kind": wrong_product["kind"],
                            "name": wrong_product["name"],
                            "sha256": wrong_product["sha256"],
                        }
                    ],
                },
                separators=(",", ":"),
                sort_keys=True,
            )
            tampered_content = (
                json.dumps(record, indent=2, sort_keys=True) + "\n"
            ).encode("utf-8")
            tampered_sha256 = harness.sha256_bytes(tampered_content)
            artifact["sha256"] = tampered_sha256
            artifact["artifact"] = harness.retain_evidence_blob(
                out_dir, "artifacts", tampered_sha256, tampered_content
            )
            matrix_path.write_text(
                json.dumps(matrix, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "product receipt disagrees with provider case binding",
            ):
                harness.verify_matrix_artifact(matrix_path)

    def test_validation_identity_is_deterministic_and_sensitive(self) -> None:
        inputs = (
            harness.ValidationInput("corpus", "corpus.json", "0" * 64),
            harness.ValidationInput("adapter-config", "v8.json", "1" * 64),
        )
        product = harness.ValidationProduct(
            "v8", "wasm-module", "module.wasm", "2" * 64
        )
        selection = harness.validation_selection_sha256(
            inputs[0].sha256, ["first", "second"]
        )
        run = harness.validation_run_sha256(
            selection,
            ["native", "v8"],
            [("native", "v8")],
            inputs,
            [product],
        )
        self.assertEqual(
            run,
            harness.validation_run_sha256(
                selection,
                ["native", "v8"],
                [("native", "v8")],
                inputs,
                [product],
            ),
        )
        self.assertNotEqual(
            selection,
            harness.validation_selection_sha256(
                inputs[0].sha256, ["second", "first"]
            ),
        )
        self.assertNotEqual(
            run,
            harness.validation_run_sha256(
                selection,
                ["native", "v8"],
                [("v8", "native")],
                inputs,
                [product],
            ),
        )
        self.assertNotEqual(
            run,
            harness.validation_run_sha256(
                selection,
                ["native", "v8"],
                [("native", "v8")],
                inputs,
                [
                    harness.ValidationProduct(
                        "v8", "wasm-module", "module.wasm", "3" * 64
                    )
                ],
            ),
        )
        self.assertNotEqual(
            run,
            harness.validation_run_sha256(
                selection,
                ["native", "v8"],
                [("native", "v8")],
                inputs,
                [product],
                build_inputs=[
                    harness.ValidationBuildInput(
                        "v8",
                        "lean-olean",
                        "Fir/Wasm/Emit/Source.olean",
                        "5" * 64,
                    )
                ],
            ),
        )
        self.assertNotEqual(
            run,
            harness.validation_run_sha256(
                selection,
                ["native", "v8"],
                [("native", "v8")],
                inputs,
                [product],
                [
                    harness.ValidationTool(
                        "v8", "engine", "v8", "4" * 64
                    )
                ],
            ),
        )

    def test_matrix_products_are_sorted_and_unique(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            descriptors = [descriptor("case")]
            context = harness.RunContext(
                harness.ROOT, out_dir, descriptors, ["case"]
            )
            products = (
                harness.ValidationProduct(
                    "v8",
                    "wasm-module",
                    "modules/z.wasm",
                    harness.sha256_bytes(b"wasm"),
                ),
                harness.ValidationProduct(
                    "v8",
                    "debug-info",
                    "modules/z.map",
                    harness.sha256_bytes(b"map"),
                ),
            )
            (out_dir / "v8" / "modules").mkdir(parents=True)
            (out_dir / "v8" / "modules" / "z.wasm").write_bytes(b"wasm")
            (out_dir / "v8" / "modules" / "z.map").write_bytes(b"map")
            engine_path = out_dir / "engine"
            runner_path = out_dir / "runner.mjs"
            engine_path.write_bytes(b"engine")
            runner_path.write_bytes(b"runner")
            tools = (
                harness.validation_tool_from_file(
                    "v8", "runner", "runner.mjs", runner_path
                ),
                harness.validation_tool_from_file(
                    "v8", "engine", "v8-engine", engine_path
                ),
            )
            harness.write_matrix_artifact(
                context, ["v8"], [], [], products, tools
            )
            matrix_path = out_dir / "matrix.json"
            first = matrix_path.read_bytes()
            matrix = json.loads(first)
            self.assertEqual(
                [product["kind"] for product in matrix["products"]],
                ["debug-info", "wasm-module"],
            )
            self.assertEqual(matrix["summary"]["productCount"], 2)
            self.assertEqual(
                [tool["kind"] for tool in matrix["tools"]],
                ["engine", "runner"],
            )
            self.assertEqual(matrix["summary"]["toolCount"], 2)
            harness.write_matrix_artifact(
                context,
                ["v8"],
                [],
                [],
                tuple(reversed(products)),
                tuple(reversed(tools)),
            )
            self.assertEqual(first, matrix_path.read_bytes())

            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate backend products"
            ):
                harness.write_matrix_artifact(
                    context,
                    ["v8"],
                    [],
                    [],
                    (products[0], products[0]),
                )
            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate backend tools"
            ):
                harness.write_matrix_artifact(
                    context,
                    ["v8"],
                    [],
                    [],
                    products,
                    (tools[0], tools[0]),
                )

    def test_product_receipts_allow_per_case_subsets_and_require_attestation(self) -> None:
        first = harness.ValidationProduct(
            "v8", "wasm-module", "modules/first.wasm", "1" * 64
        )
        second = harness.ValidationProduct(
            "v8", "wasm-module", "modules/second.wasm", "2" * 64
        )

        def received(case_id: str, products: list[harness.ValidationProduct]) -> dict:
            record = success(case_id, "v8")
            record["diagnostics"] = [
                {
                    "key": "validation-products",
                    "value": harness.product_receipt_value(products),
                }
            ]
            return record

        backend_run = harness.BackendRun(
            "v8",
            ["first", "second"],
            results={
                "first": received("first", [first]),
                "second": received("second", [second]),
            },
            products=[second, first],
        )
        self.assertEqual(harness.product_receipt_findings(backend_run), [])

        backend_run.results["second"] = success("second", "v8")
        self.assertEqual(
            finding_messages(harness.product_receipt_findings(backend_run)),
            ["second: missing validation-products diagnostic"],
        )

        unknown = harness.ValidationProduct(
            "v8", "wasm-module", "modules/ghost.wasm", "3" * 64
        )
        backend_run.results["second"] = received("second", [second, unknown])
        self.assertEqual(
            finding_messages(harness.product_receipt_findings(backend_run)),
            [
                "second: product receipt contains undeclared products: "
                "wasm-module:modules/ghost.wasm@" + "3" * 64
            ],
        )

        malformed = success("second", "v8")
        malformed["diagnostics"] = [
            {"key": "validation-products", "value": "not-json"}
        ]
        backend_run.results["second"] = malformed
        self.assertEqual(
            finding_messages(harness.product_receipt_findings(backend_run)),
            ["second: malformed validation-products diagnostic"],
        )

        backend_run.results["second"] = received("second", [])
        self.assertEqual(
            finding_messages(harness.product_receipt_findings(backend_run)),
            [
                "second: validation-products diagnostic reports no consumed products"
            ],
        )

    def test_pair_spec_is_directed_and_strict(self) -> None:
        self.assertEqual(
            harness.parse_pair_spec("v8:talos"), ("v8", "talos")
        )
        with self.assertRaisesRegex(harness.ValidationError, "REFERENCE:CANDIDATE"):
            harness.parse_pair_spec("native-lcnf")
        with self.assertRaisesRegex(harness.ValidationError, "distinct backends"):
            harness.parse_pair_spec("native:native")

    def test_external_adapter_config_uses_argv_not_a_shell_command(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "configs" / "v8.json"
            path.parent.mkdir()
            path.write_text(
                json.dumps(
                    {
                        "name": "v8",
                        "buildCommand": ["node", "scripts/build-v8.mjs"],
                        "runCommand": ["node", "scripts/run-v8.mjs"],
                        "resultDomain": "selected",
                        "timeoutSeconds": 30,
                        "products": [
                            {
                                "kind": "wasm-module",
                                "path": "modules/validation.wasm",
                            }
                        ],
                        "buildTools": [
                            {
                                "kind": "build-driver",
                                "name": "scripts/build-v8.mjs",
                                "path": "../scripts/build-v8.mjs",
                            },
                            {
                                "kind": "build-launcher",
                                "name": "node",
                                "command": "node",
                            },
                        ],
                        "tools": [
                            {
                                "kind": "runner",
                                "name": "scripts/run-v8.mjs",
                                "path": "../scripts/run-v8.mjs",
                            },
                            {
                                "kind": "engine",
                                "name": "node",
                                "command": "node",
                            },
                        ],
                    }
                ),
                encoding="utf-8",
            )
            adapter = harness.external_adapter_from_config(path)
            self.assertEqual(adapter.name, "v8")
            self.assertEqual(adapter.run_command, ["node", "scripts/run-v8.mjs"])
            self.assertEqual(adapter.result_domain, "selected")
            self.assertEqual(adapter.timeout_seconds, 30)
            self.assertEqual(adapter.build_attempts, 1)
            self.assertEqual(
                adapter.product_declarations,
                (
                    harness.ProductDeclaration(
                        "wasm-module", "modules/validation.wasm"
                    ),
                ),
            )
            self.assertEqual(
                adapter.build_tool_declarations,
                (
                    harness.ToolDeclaration(
                        "build-driver",
                        "scripts/build-v8.mjs",
                        path=root / "scripts" / "build-v8.mjs",
                    ),
                    harness.ToolDeclaration(
                        "build-launcher", "node", command="node"
                    ),
                ),
            )
            self.assertEqual(
                adapter.tool_declarations,
                (
                    harness.ToolDeclaration(
                        "engine", "node", command="node"
                    ),
                    harness.ToolDeclaration(
                        "runner",
                        "scripts/run-v8.mjs",
                        path=root / "scripts" / "run-v8.mjs",
                    ),
                ),
            )

            value = json.loads(path.read_text(encoding="utf-8"))
            value["runCommand"] = "node scripts/run-v8.mjs"
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(harness.ValidationError, "argv array"):
                harness.external_adapter_from_config(path)

    def test_strace_file_access_parser_is_strict_and_canonical(self) -> None:
        trace = "\n".join(
            [
                '101 execve("/opt/bin/tool", ["tool"], 0x0) = 0',
                '101 openat(0xffffff9c, "/opt/input", 0x80000)     = 3</opt/input>',
                '101 openat(0xffffff9c, "/opt/deleted", 0x80000) = 12</opt/deleted>(deleted)',
                '101 open("/opt/read-write", 0x2) = 4</opt/read-write>',
                '101 open("/opt/default-flags", 0) = 9</opt/default-flags>',
                '101 open("/opt/name = value", 0) = 10</opt/name = value>',
                '101 openat2(0xffffff9c, "/opt/openat2", {flags=0, mode=0, resolve=0}, 0x18) = 11</opt/openat2>',
                '101 openat(0xffffff9c, "/opt/output", 0x80241) = 5</opt/output>',
                '101 openat(0xffffff9c, "/opt/metadata", 0x200000) = 6</opt/metadata>',
                '102 execveat(7</opt/bin>, "helper", ["helper"], 0x0, 0x0) = 0',
                '102 openat(0xffffff9c, "/opt/bin/tool", 0x0) = 8</opt/bin/tool>',
            ]
        ).encode("utf-8")
        self.assertEqual(
            core.parse_build_file_access_trace(trace, "fixture"),
            {
                "/opt/bin/helper": ("exec",),
                "/opt/bin/tool": ("exec", "read"),
                "/opt/default-flags": ("read",),
                "/opt/deleted": ("read",),
                "/opt/input": ("read",),
                "/opt/name = value": ("read",),
                "/opt/openat2": ("read",),
                "/opt/read-write": ("read",),
            },
        )
        malformed_traces = [
            (
                b'101 execve("relative", ["relative"], 0x0) = 0',
                "not absolute",
            ),
            (
                b'101 openat(0xffffff9c, "/opt/input", 0x0) = 3',
                "malformed traced openat result",
            ),
            (
                b'101 openat(0xffffff9c, "/opt/input", 0x0 <unfinished ...>',
                "incomplete traced openat syscall",
            ),
            (
                b'101 <... openat resumed>) = 3</opt/input>',
                "resumed traced openat syscall is ambiguous",
            ),
            (
                b'101 execve("/opt/bin/tool", ["tool"], 0x0) = -1',
                "traced execve did not succeed",
            ),
            (
                b'101 --- SIGCHLD {si_signo=SIGCHLD} ---',
                "unrecognized strace line",
            ),
        ]
        for malformed, message in malformed_traces:
            with self.subTest(message=message):
                with self.assertRaisesRegex(
                    harness.ValidationError, message
                ):
                    core.parse_build_file_access_trace(
                        malformed, "fixture"
                    )

    def test_bwrap_status_parser_is_strict(self) -> None:
        namespace = {
            "child-pid": 101,
            "cgroup-namespace": 102,
            "ipc-namespace": 103,
            "mnt-namespace": 104,
            "net-namespace": 105,
            "pid-namespace": 106,
            "uts-namespace": 107,
        }
        exit_status = {"exit-code": 0}
        content = (
            json.dumps(namespace) + "\n" + json.dumps(exit_status) + "\n"
        ).encode("utf-8")
        self.assertEqual(
            core.parse_bwrap_status(content, "fixture"),
            (namespace, exit_status),
        )

        malformed = (
            b"\xff",
            b"not-json\n",
            (json.dumps(namespace) + "\n").encode("utf-8"),
            (
                json.dumps(namespace | {"extra": 1})
                + "\n"
                + json.dumps(exit_status)
                + "\n"
            ).encode("utf-8"),
            (
                json.dumps(namespace | {"child-pid": True})
                + "\n"
                + json.dumps(exit_status)
                + "\n"
            ).encode("utf-8"),
            (
                json.dumps(namespace | {"child-pid": 0})
                + "\n"
                + json.dumps(exit_status)
                + "\n"
            ).encode("utf-8"),
            (
                json.dumps(namespace)
                + "\n"
                + json.dumps({"exit-code": 1})
                + "\n"
            ).encode("utf-8"),
        )
        for content in malformed:
            with self.subTest(content=content):
                with self.assertRaisesRegex(
                    harness.ValidationError, "malformed sandbox status"
                ):
                    core.parse_bwrap_status(content, "fixture")

    def test_sealed_snapshot_fd_has_exact_content_mode_and_seals(self) -> None:
        content = b"content-addressed replay input"
        digest = harness.sha256_bytes(content)
        expected_seals = (
            fcntl.F_SEAL_WRITE
            | fcntl.F_SEAL_GROW
            | fcntl.F_SEAL_SHRINK
            | fcntl.F_SEAL_SEAL
        )
        for mode in (0o444, 0o555):
            with self.subTest(mode=oct(mode)):
                descriptor = core.sealed_snapshot_fd(
                    digest, content, mode, "fixture"
                )
                try:
                    self.assertGreaterEqual(descriptor, 64)
                    self.assertEqual(
                        Path(f"/proc/self/fd/{descriptor}").read_bytes(),
                        content,
                    )
                    metadata = os.fstat(descriptor)
                    self.assertEqual(metadata.st_mode & 0o777, mode)
                    self.assertEqual(
                        fcntl.fcntl(descriptor, fcntl.F_GET_SEALS),
                        expected_seals,
                    )
                    with self.assertRaises(OSError):
                        os.write(descriptor, b"tamper")
                    with self.assertRaises(OSError):
                        os.ftruncate(descriptor, 0)
                finally:
                    os.close(descriptor)

        with self.assertRaisesRegex(
            harness.ValidationError, "malformed SHA-256"
        ):
            core.sealed_snapshot_fd("bad", content, 0o444, "fixture")
        with self.assertRaisesRegex(
            harness.ValidationError, "snapshot content digest mismatch"
        ):
            core.sealed_snapshot_fd(digest, b"different", 0o444, "fixture")
        with self.assertRaisesRegex(
            harness.ValidationError, "invalid snapshot mode"
        ):
            core.sealed_snapshot_fd(digest, content, 0o644, "fixture")

    def test_external_adapter_tool_config_is_strict(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "v8.json"
            base = {
                "name": "v8",
                "runCommand": ["node", "run.mjs"],
                "resultDomain": "selected",
            }

            path.write_text(json.dumps(base), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "tools must be nonempty"
            ):
                harness.external_adapter_from_config(path)

            invalid_tools = (
                [{"kind": "engine", "name": "node"}],
                [
                    {
                        "kind": "engine",
                        "name": "node",
                        "command": "node",
                        "path": "node",
                    }
                ],
                [
                    {
                        "kind": "engine",
                        "name": "node",
                        "command": "node",
                        "extra": True,
                    }
                ],
            )
            for tools in invalid_tools:
                value = dict(base)
                value["tools"] = tools
                path.write_text(json.dumps(value), encoding="utf-8")
                with self.assertRaisesRegex(
                    harness.ValidationError, "exactly one of path or command"
                ):
                    harness.external_adapter_from_config(path)

            for tool_path in (
                "/tmp/runner.mjs",
                "a/../runner.mjs",
                "runner\\module.mjs",
            ):
                value = dict(base)
                value["tools"] = [
                    {
                        "kind": "runner",
                        "name": "runner.mjs",
                        "path": tool_path,
                    }
                ]
                path.write_text(json.dumps(value), encoding="utf-8")
                with self.assertRaisesRegex(
                    harness.ValidationError, "config-relative POSIX path"
                ):
                    harness.external_adapter_from_config(path)

            value = dict(base)
            value["tools"] = [
                {
                    "kind": "runner",
                    "name": "../runner.mjs",
                    "path": "runner.mjs",
                }
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "normalized relative POSIX path"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["tools"] = [
                {"kind": "engine", "name": "node", "command": ""}
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "command must be a bare PATH command"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["tools"] = [
                {
                    "kind": "engine",
                    "name": "node",
                    "command": "/usr/bin/node",
                }
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "command must be a bare PATH command"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["tools"] = [
                {"kind": "engine", "name": "node", "command": "node"},
                {"kind": "engine", "name": "node", "path": "node"},
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate tool: engine:node"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["tools"] = [
                {"kind": "engine", "name": "node", "command": "node"},
                {
                    "kind": "secondary",
                    "name": "node-copy",
                    "command": "node",
                },
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate tool source: node"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["tools"] = {"kind": "engine"}
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "tools must be an object array"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["tools"] = [
                {
                    "kind": "engine",
                    "name": "node",
                    "command": "other-engine",
                }
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, r"must match runCommand\[0\]"
            ):
                harness.external_adapter_from_config(path)

    def test_external_adapter_build_tool_config_is_strict(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "v8.json"
            base = {
                "name": "v8",
                "buildCommand": ["node", "build.mjs"],
                "runCommand": ["node", "run.mjs"],
                "resultDomain": "selected",
                "tools": [
                    {"kind": "engine", "name": "node", "command": "node"}
                ],
            }

            path.write_text(json.dumps(base), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "buildTools must be nonempty"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["buildTools"] = [
                {
                    "kind": "build-launcher",
                    "name": "other",
                    "command": "other",
                }
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, r"must match buildCommand\[0\]"
            ):
                harness.external_adapter_from_config(path)

            del value["buildCommand"]
            value["buildTools"] = [
                {
                    "kind": "build-launcher",
                    "name": "node-build",
                    "command": "node",
                }
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "buildTools requires buildCommand"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["buildTools"] = [
                {
                    "kind": "engine",
                    "name": "node",
                    "command": "node",
                }
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate tool across build and run"
            ):
                harness.external_adapter_from_config(path)

    def test_external_adapter_file_access_recorder_config_is_strict(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "v8.json"
            base = {
                "name": "v8",
                "buildCommand": ["node", "build.mjs"],
                "runCommand": ["node", "run.mjs"],
                "resultDomain": "selected",
                "buildInputManifest": "build-inputs.json",
                "buildTools": [
                    {
                        "kind": "build-launcher",
                        "name": "node-build",
                        "command": "node",
                    }
                ],
                "tools": [
                    {"kind": "engine", "name": "node", "command": "node"}
                ],
                "buildFileAccessRecorder": {
                    "kind": "file-access-recorder",
                    "name": "strace",
                    "command": "strace",
                },
            }
            path.write_text(json.dumps(base), encoding="utf-8")
            adapter = harness.external_adapter_from_config(path)
            self.assertEqual(
                adapter.build_file_access_recorder,
                harness.ToolDeclaration(
                    "file-access-recorder", "strace", command="strace"
                ),
            )

            invalid = dict(base)
            invalid["buildFileAccessRecorder"] = {}
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "expected kind, name, and command fields",
            ):
                harness.external_adapter_from_config(path)

            invalid = dict(base)
            invalid["buildFileAccessRecorder"] = {
                "kind": "file-access-recorder",
                "name": "strace",
                "command": "./strace",
            }
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "bare PATH command"
            ):
                harness.external_adapter_from_config(path)

            invalid = dict(base)
            del invalid["buildInputManifest"]
            path.write_text(json.dumps(invalid), encoding="utf-8")
            self.assertIsNotNone(
                harness.external_adapter_from_config(
                    path
                ).build_file_access_recorder
            )

            invalid = dict(base)
            del invalid["buildCommand"]
            del invalid["buildTools"]
            del invalid["buildInputManifest"]
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "buildFileAccessRecorder requires buildCommand",
            ):
                harness.external_adapter_from_config(path)

            invalid = dict(base)
            invalid["buildFileAccessRecorder"] = {
                "kind": "tracer",
                "name": "strace",
                "command": "strace",
            }
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "kind must be file-access-recorder",
            ):
                harness.external_adapter_from_config(path)

            invalid = dict(base)
            invalid["buildTools"] = [
                {
                    "kind": "file-access-recorder",
                    "name": "node-build",
                    "command": "node",
                }
            ]
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "tool kind is reserved for buildFileAccessRecorder",
            ):
                harness.external_adapter_from_config(path)

            invalid = dict(base)
            invalid["buildFileAccessRecorder"] = {
                "kind": "file-access-recorder",
                "name": "node-recorder",
                "command": "node",
            }
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "duplicate file-access recorder source",
            ):
                harness.external_adapter_from_config(path)

    def test_external_adapter_execution_recorder_config_is_strict(self) -> None:
        contract = harness.ProductContract(
            "wasm", "wasm32", "fixture-runtime", "fixture-abi"
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "v8.json"
            base = fixture_consumer_config(
                "v8", "fixture-wasm", contract
            )
            base["executionFileAccessRecorder"] = {
                "kind": "execution-file-access-recorder",
                "name": "strace",
                "command": "strace",
            }
            path.write_text(json.dumps(base), encoding="utf-8")
            adapter = harness.external_adapter_from_config(path)
            self.assertEqual(
                adapter.execution_file_access_recorder,
                harness.ToolDeclaration(
                    "execution-file-access-recorder",
                    "strace",
                    command="strace",
                ),
            )

            invalid = json.loads(json.dumps(base))
            invalid["executionFileAccessRecorder"] = {}
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "expected kind, name, and command fields",
            ):
                harness.external_adapter_from_config(path)

            invalid = json.loads(json.dumps(base))
            invalid["executionFileAccessRecorder"]["kind"] = (
                "file-access-recorder"
            )
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "kind must be execution-file-access-recorder",
            ):
                harness.external_adapter_from_config(path)

            invalid = json.loads(json.dumps(base))
            invalid["executionFileAccessRecorder"]["command"] = "./strace"
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "bare PATH command"
            ):
                harness.external_adapter_from_config(path)

            invalid = json.loads(json.dumps(base))
            invalid["executionFileAccessRecorder"]["command"] = "trace-tool"
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "name must equal command",
            ):
                harness.external_adapter_from_config(path)

            invalid = json.loads(json.dumps(base))
            del invalid["productProvider"]
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "executionFileAccessRecorder requires productProvider",
            ):
                harness.external_adapter_from_config(path)

            invalid = json.loads(json.dumps(base))
            invalid["tools"][0]["kind"] = (
                "execution-file-access-recorder"
            )
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "tool kind is reserved for executionFileAccessRecorder",
            ):
                harness.external_adapter_from_config(path)

            invalid = json.loads(json.dumps(base))
            python_command = Path(sys.executable).name
            invalid["executionFileAccessRecorder"]["name"] = python_command
            invalid["executionFileAccessRecorder"]["command"] = python_command
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "duplicate execution file-access recorder source",
            ):
                harness.external_adapter_from_config(path)

    def test_execution_recorder_closes_receipts_over_opened_products(self) -> None:
        contract = harness.ProductContract(
            "wasm", "wasm32", "fixture-runtime", "fixture-abi"
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            product_path = out_dir / "fixture-wasm" / "module.wasm"
            product_path.parent.mkdir(parents=True)
            product_content = b"fixture-wasm"
            product_path.write_bytes(product_content)
            product = harness.ValidationProduct(
                "fixture-wasm",
                "wasm-module",
                "module.wasm",
                harness.sha256_bytes(product_content),
            )
            case_products = (("case", (product,)),)
            bundle = harness.ProductBundle(
                "fixture-wasm",
                contract,
                core.product_bundle_sha256(
                    "fixture-wasm",
                    contract,
                    (product,),
                    case_products,
                ),
                (product,),
                case_products,
            )
            adapter = harness.ExternalCommandAdapter(
                "v8",
                [],
                "selected",
                product_provider=harness.ProductProviderRequirement(
                    bundle.provider, contract
                ),
                execution_file_access_recorder=harness.ToolDeclaration(
                    "execution-file-access-recorder",
                    "strace",
                    command="strace",
                ),
            )
            recorder = harness.ValidationTool(
                "v8",
                "execution-file-access-recorder",
                "strace",
                "1" * 64,
            )
            adapter._built_execution_file_access_recorder = recorder
            (out_dir / "v8").mkdir(parents=True)
            record = success("case", "v8")
            record["diagnostics"] = [
                {
                    "key": core.PRODUCT_BUNDLE_RECEIPT_DIAGNOSTIC,
                    "value": harness.product_bundle_receipt_value(
                        bundle, "case"
                    ),
                }
            ]
            normalized_product_path = os.path.normpath(
                str(product_path.resolve())
            )
            trace_content = (
                "1 openat(-100</>, "
                f"{json.dumps(normalized_product_path)}, 0x80000) = "
                f"3<{normalized_product_path}>\n"
            ).encode("utf-8")
            trace_digest = harness.sha256_bytes(trace_content)
            trace_name = "v8/execute/file-access.strace"
            context = harness.RunContext(
                root,
                out_dir,
                [descriptor("case")],
                ["case"],
                product_bundles={bundle.provider: bundle},
            )
            report_artifacts = adapter.execution_file_access_artifact(
                context,
                bundle,
                {"case": record},
                (
                    {"name": trace_name, "sha256": trace_digest},
                    {normalized_product_path: ("read",)},
                ),
            )
            self.assertEqual(len(report_artifacts), 1)
            report = json.loads(
                report_artifacts[0].content.decode("utf-8")
            )
            self.assertEqual(report["receiptCount"], 1)
            self.assertEqual(report["productCount"], 1)
            trace_artifact = harness.ValidationArtifact(
                "execution-file-access-trace",
                trace_name,
                trace_digest,
                trace_content,
            )
            consumer = harness.ProductConsumer(
                "v8", bundle.provider, contract, bundle.bundle_sha256
            )
            receipt = harness.ProductReceipt(
                "v8",
                "case",
                bundle.provider,
                bundle.bundle_sha256,
                (product,),
            )
            core.verify_execution_file_access_evidence(
                {"v8": report},
                {"v8": trace_artifact},
                {"v8": adapter},
                ["v8"],
                [recorder],
                [bundle],
                [consumer],
                [receipt],
            )
            coverage = core.validation_coverage_report(
                ["case"],
                ["v8"],
                [],
                [bundle.provider, None],
                [bundle],
                [consumer],
                [receipt],
                {("case", "v8"): record},
                {"v8": report},
            )
            self.assertEqual(
                coverage["consumers"][0]["executionAccess"],
                {
                    "recorded": True,
                    "recorder": "strace",
                    "openedReceiptedProductCount": 1,
                    "traceAccessCount": 1,
                },
            )
            self.assertEqual(coverage["findingCount"], 2)
            self.assertEqual(coverage["unassignedFindingCount"], 1)
            self.assertEqual(coverage["providers"][0]["findingCount"], 1)
            self.assertIn(
                "opened 1/1 unique products with strace",
                "\n".join(core.render_validation_coverage(coverage)),
            )
            telemetry_only = json.loads(json.dumps(coverage))
            telemetry_only["consumers"][0]["executionAccess"][
                "traceAccessCount"
            ] += 1
            self.assertNotEqual(coverage, telemetry_only)
            self.assertEqual(
                core.evidence_coverage_claim(coverage),
                core.evidence_coverage_claim(telemetry_only),
            )

            with self.assertRaisesRegex(
                harness.ValidationError,
                "execution did not open receipted product",
            ):
                adapter.execution_file_access_artifact(
                    context,
                    bundle,
                    {"case": record},
                    (
                        {"name": trace_name, "sha256": "2" * 64},
                        {"/bin/true": ("exec",)},
                    ),
                )

            missing_content = b'1 execve("/bin/true", [], 0x0) = 0\n'
            missing_digest = harness.sha256_bytes(missing_content)
            missing_report = json.loads(json.dumps(report))
            missing_report["trace"]["sha256"] = missing_digest
            missing_report["accessCount"] = 1
            with self.assertRaisesRegex(
                harness.ValidationError,
                "product disagrees with trace",
            ):
                core.verify_execution_file_access_evidence(
                    {"v8": missing_report},
                    {
                        "v8": harness.ValidationArtifact(
                            "execution-file-access-trace",
                            trace_name,
                            missing_digest,
                            missing_content,
                        )
                    },
                    {"v8": adapter},
                    ["v8"],
                    [recorder],
                    [bundle],
                    [consumer],
                    [receipt],
                )

            with self.assertRaisesRegex(
                harness.ValidationError,
                "configs, tools, reports, and traces disagree",
            ):
                core.verify_execution_file_access_evidence(
                    {"v8": report},
                    {"v8": trace_artifact},
                    {},
                    ["v8"],
                    [recorder],
                    [bundle],
                    [consumer],
                    [receipt],
                )

    def test_external_adapter_build_input_replay_config_is_strict(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "v8.json"
            base = {
                "name": "v8",
                "buildCommand": ["node", "build.mjs"],
                "buildReplayCommand": ["node", "replay.mjs"],
                "runCommand": ["node", "run.mjs"],
                "resultDomain": "selected",
                "products": [
                    {"kind": "wasm-module", "path": "module.wasm"}
                ],
                "buildInputManifest": "build-inputs.json",
                "buildTools": [
                    {
                        "kind": "build-launcher",
                        "name": "node-build",
                        "command": "node",
                    }
                ],
                "tools": [
                    {"kind": "engine", "name": "node", "command": "node"}
                ],
                "buildFileAccessRecorder": {
                    "kind": "file-access-recorder",
                    "name": "strace",
                    "command": "strace",
                },
                "buildInputReplay": {
                    "kind": "build-input-replay-isolator",
                    "name": "bwrap",
                    "command": "bwrap",
                },
            }

            def copy_base() -> dict:
                return json.loads(json.dumps(base))

            path.write_text(json.dumps(base), encoding="utf-8")
            adapter = harness.external_adapter_from_config(path)
            self.assertEqual(
                adapter.build_replay_command,
                ["node", "replay.mjs"],
            )
            self.assertEqual(
                adapter.build_input_replay_isolator,
                harness.ToolDeclaration(
                    "build-input-replay-isolator",
                    "bwrap",
                    command="bwrap",
                ),
            )

            with_resolver = copy_base()
            with_resolver["buildTools"][0]["resolveCommand"] = [
                "node",
                "resolve-node.mjs",
            ]
            path.write_text(json.dumps(with_resolver), encoding="utf-8")
            resolved_adapter = harness.external_adapter_from_config(path)
            self.assertEqual(
                resolved_adapter.build_tool_declarations[0],
                harness.ToolDeclaration(
                    "build-launcher",
                    "node-build",
                    command="node",
                    resolve_command=("node", "resolve-node.mjs"),
                ),
            )

            for malformed_resolver in (
                [],
                "node resolve-node.mjs",
                ["node", ""],
                ["node", 1],
            ):
                invalid = copy_base()
                invalid["buildTools"][0]["resolveCommand"] = (
                    malformed_resolver
                )
                path.write_text(json.dumps(invalid), encoding="utf-8")
                with self.subTest(resolve_command=malformed_resolver):
                    with self.assertRaisesRegex(
                        harness.ValidationError,
                        "resolveCommand must be a nonempty argv array",
                    ):
                        harness.external_adapter_from_config(path)

            invalid = copy_base()
            invalid["buildTools"] = [
                {
                    "kind": "build-driver",
                    "name": "build.mjs",
                    "path": "build.mjs",
                    "resolveCommand": ["node", "resolve-node.mjs"],
                }
            ]
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "resolveCommand requires command",
            ):
                harness.external_adapter_from_config(path)

            invalid = copy_base()
            invalid["buildReplayCommand"] = "node replay.mjs"
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "buildReplayCommand must be an argv array",
            ):
                harness.external_adapter_from_config(path)

            invalid = copy_base()
            invalid["buildReplayCommand"][0] = "python3"
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "buildTools command tool must match buildReplayCommand",
            ):
                harness.external_adapter_from_config(path)

            invalid = copy_base()
            del invalid["buildInputReplay"]
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "buildReplayCommand requires buildInputReplay",
            ):
                harness.external_adapter_from_config(path)

            invalid = copy_base()
            invalid["buildInputReplay"] = {}
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "expected kind, name, and command fields",
            ):
                harness.external_adapter_from_config(path)

            invalid = copy_base()
            invalid["buildInputReplay"]["kind"] = "sandbox"
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "kind must be build-input-replay-isolator",
            ):
                harness.external_adapter_from_config(path)

            invalid = copy_base()
            invalid["buildInputReplay"]["command"] = "./bwrap"
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "bare PATH command"
            ):
                harness.external_adapter_from_config(path)

            for missing, message in (
                (
                    "buildReplayCommand",
                    "buildInputReplay requires buildReplayCommand",
                ),
                (
                    "buildInputManifest",
                    "buildInputReplay requires buildInputManifest",
                ),
                (
                    "buildFileAccessRecorder",
                    "buildInputReplay requires buildFileAccessRecorder",
                ),
            ):
                invalid = copy_base()
                del invalid[missing]
                path.write_text(json.dumps(invalid), encoding="utf-8")
                with self.subTest(missing=missing):
                    with self.assertRaisesRegex(
                        harness.ValidationError, message
                    ):
                        harness.external_adapter_from_config(path)

            invalid = copy_base()
            invalid["buildInputReplay"]["command"] = "strace"
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "duplicate build-input replay source",
            ):
                harness.external_adapter_from_config(path)

            invalid = copy_base()
            invalid["buildTools"][0]["kind"] = (
                "build-input-replay-isolator"
            )
            path.write_text(json.dumps(invalid), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "tool kind is reserved for buildInputReplay",
            ):
                harness.external_adapter_from_config(path)

    def test_external_adapter_product_config_is_strict(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "v8.json"
            base = {
                "name": "v8",
                "buildCommand": ["node", "build.mjs"],
                "runCommand": ["node", "run.mjs"],
                "resultDomain": "selected",
                "buildTools": [
                    {
                        "kind": "build-launcher",
                        "name": "node-build",
                        "command": "node",
                    }
                ],
                "tools": [
                    {"kind": "engine", "name": "node", "command": "node"}
                ],
            }

            for product_path in (
                "../escape.wasm",
                "/tmp/escape.wasm",
                "a/./b",
                ".",
                "modules\\validation.wasm",
            ):
                value = dict(base)
                value["products"] = [
                    {"kind": "wasm-module", "path": product_path}
                ]
                path.write_text(json.dumps(value), encoding="utf-8")
                with self.assertRaisesRegex(
                    harness.ValidationError, "normalized relative POSIX path"
                ):
                    harness.external_adapter_from_config(path)

            value = dict(base)
            value["products"] = [
                {"kind": "wasm-module", "path": "module.wasm"},
                {"kind": "debug-info", "path": "module.wasm"},
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate product path"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            del value["buildCommand"]
            value["products"] = [
                {"kind": "wasm-module", "path": "module.wasm"}
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "products require buildCommand"
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["buildAttempts"] = 2
            value["products"] = [
                {"kind": "wasm-module", "path": "module.wasm"}
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            self.assertEqual(
                harness.external_adapter_from_config(path).build_attempts,
                2,
            )

            for attempts in (0, -1, True, "2"):
                value["buildAttempts"] = attempts
                path.write_text(json.dumps(value), encoding="utf-8")
                with self.assertRaisesRegex(
                    harness.ValidationError,
                    "buildAttempts must be a positive integer",
                ):
                    harness.external_adapter_from_config(path)

            value = dict(base)
            value["buildAttempts"] = 2
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "multiple buildAttempts require products",
            ):
                harness.external_adapter_from_config(path)

            value = dict(base)
            value["productManifest"] = "products.json"
            path.write_text(json.dumps(value), encoding="utf-8")
            adapter = harness.external_adapter_from_config(path)
            self.assertEqual(adapter.product_manifest, "products.json")
            self.assertEqual(adapter.product_declarations, ())

            value["products"] = [
                {"kind": "wasm-module", "path": "module.wasm"}
            ]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "mutually exclusive"
            ):
                harness.external_adapter_from_config(path)

            del value["products"]
            del value["buildCommand"]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "requires buildCommand"
            ):
                harness.external_adapter_from_config(path)

            for manifest_path in (
                "../products.json",
                "/tmp/products.json",
                "build/stdout.jsonl",
                "execution-input.json",
            ):
                value = dict(base)
                value["productManifest"] = manifest_path
                path.write_text(json.dumps(value), encoding="utf-8")
                with self.assertRaisesRegex(
                    harness.ValidationError,
                    "normalized relative POSIX path|reserved by the harness",
                ):
                    harness.external_adapter_from_config(path)

            value = dict(base)
            value["buildInputManifest"] = "build-inputs.json"
            path.write_text(json.dumps(value), encoding="utf-8")
            adapter = harness.external_adapter_from_config(path)
            self.assertEqual(
                adapter.build_input_manifest, "build-inputs.json"
            )

            value["productManifest"] = "build-inputs.json"
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "collides with a product path"
            ):
                harness.external_adapter_from_config(path)

            del value["productManifest"]
            del value["buildCommand"]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "requires buildCommand"
            ):
                harness.external_adapter_from_config(path)

    def test_dynamic_product_manifest_is_captured_and_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            backend_dir = out_dir / "v8"
            module = backend_dir / "modules" / "module.wasm"
            module.parent.mkdir(parents=True)
            module.write_bytes(b"wasm product")
            manifest = backend_dir / "products.json"
            manifest_value = {
                "version": 3,
                "products": [
                    {"kind": "wasm-module", "path": "modules/module.wasm"}
                ],
            }
            manifest.write_text(json.dumps(manifest_value), encoding="utf-8")
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                build_command=[sys.executable, "-c", "pass"],
                run_command=[sys.executable, "-c", "pass"],
                result_domain="selected",
                product_manifest="products.json",
            )
            adapter.build(harness.BuildContext(root, out_dir, True))
            self.assertEqual(
                [(product.kind, product.name) for product in adapter._built_products],
                [
                    ("product-manifest", "products.json"),
                    ("wasm-module", "modules/module.wasm"),
                ],
            )

            manifest_value["products"].append(
                {"kind": "debug-info", "path": "modules/debug.txt"}
            )
            manifest.write_text(json.dumps(manifest_value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "product is not a regular file"
            ):
                adapter.collect_products(out_dir)

            manifest_value["products"] = [
                {"kind": "product-manifest", "path": "nested.json"}
            ]
            manifest.write_text(json.dumps(manifest_value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "product kind is reserved"
            ):
                adapter.collect_products(out_dir)

            invalid_manifests = [
                (
                    {"version": 1, "products": []},
                    "unsupported version",
                ),
                (
                    {"version": 3, "products": []},
                    "nonempty array",
                ),
                (
                    {"version": 3, "products": [], "extra": True},
                    "must contain version and products",
                ),
                (
                    {
                        "version": 3,
                        "products": [
                            {"kind": "wasm-module", "path": "module.wasm"},
                            {"kind": "debug-info", "path": "module.wasm"},
                        ],
                    },
                    "duplicate product path",
                ),
                (
                    {
                        "version": 3,
                        "products": [
                            {
                                "kind": "wasm-module",
                                "path": "build/stdout.jsonl",
                            }
                        ],
                    },
                    "reserved by the harness",
                ),
            ]
            for invalid, message in invalid_manifests:
                manifest.write_text(json.dumps(invalid), encoding="utf-8")
                with self.assertRaisesRegex(harness.ValidationError, message):
                    adapter.collect_products(out_dir)

            real_parent = backend_dir / "real"
            real_parent.mkdir()
            (real_parent / "nested.wasm").write_bytes(b"nested")
            (backend_dir / "alias").symlink_to(real_parent, target_is_directory=True)
            manifest_value["products"] = [
                {"kind": "wasm-module", "path": "alias/nested.wasm"}
            ]
            manifest.write_text(json.dumps(manifest_value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "contains a symlink"
            ):
                adapter.collect_products(out_dir)

            outside = root / "outside"
            outside.mkdir()
            marker = outside / "marker"
            marker.write_text("keep", encoding="utf-8")
            shutil.rmtree(backend_dir)
            self.assertFalse(backend_dir.exists())
            backend_dir.symlink_to(outside, target_is_directory=True)
            with self.assertRaisesRegex(
                harness.ValidationError, "not a regular directory"
            ):
                adapter.clear_dynamic_product_staging(out_dir)
            self.assertEqual(marker.read_text(encoding="utf-8"), "keep")

    def test_repeat_build_records_product_mismatch_and_executes_final(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            module = out_dir / "v8" / "module.wasm"
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                build_command=["builder"],
                run_command=["runner"],
                result_domain="selected",
                product_declarations=(
                    harness.ProductDeclaration("wasm-module", "module.wasm"),
                ),
                build_attempts=2,
            )
            attempts = 0
            completed = mock.Mock(returncode=0, stdout="", stderr="")

            def build_once(*args: object, **kwargs: object) -> mock.Mock:
                nonlocal attempts
                attempts += 1
                module.parent.mkdir(parents=True, exist_ok=True)
                module.write_bytes(
                    b"first build" if attempts == 1 else b"second build"
                )
                return completed

            with mock.patch.object(core, "run", side_effect=build_once):
                adapter.build(harness.BuildContext(root, out_dir, False))
            self.assertEqual(attempts, 2)
            self.assertEqual(len(adapter._build_findings), 1)
            self.assertEqual(
                adapter._build_findings[0].phase, "build-determinism"
            )
            report = json.loads(
                (out_dir / "v8" / "build-determinism.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertFalse(report["equal"])
            self.assertNotEqual(
                report["attempts"][0]["products"],
                report["attempts"][1]["products"],
            )
            self.assertEqual(
                adapter._built_products[0].sha256,
                harness.sha256_bytes(b"second build"),
            )

            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            run_context = harness.RunContext(
                root, out_dir, descriptors, ["case"]
            )
            execution = mock.Mock(
                returncode=0,
                stdout=json.dumps(success("case", "v8")) + "\n",
                stderr="",
            )
            with mock.patch.object(core, "run", return_value=execution):
                backend_run = adapter.execute(run_context)
            self.assertIn("case", backend_run.results)
            self.assertEqual(
                [finding.phase for finding in backend_run.findings],
                ["build-determinism"],
            )

    def test_build_file_access_recorder_covers_every_reported_input(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            source = root / "compiler.input"
            source.write_bytes(b"compiler input")
            module = out_dir / "v8" / "module.wasm"
            manifest = out_dir / "v8" / "build-inputs.json"
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                build_command=["builder"],
                run_command=["runner"],
                result_domain="selected",
                product_declarations=(
                    harness.ProductDeclaration(
                        "wasm-module", "module.wasm"
                    ),
                ),
                build_input_manifest="build-inputs.json",
                build_file_access_recorder=harness.ToolDeclaration(
                    "file-access-recorder", "strace", command="strace"
                ),
                build_attempts=2,
            )
            attempts = 0
            completed = mock.Mock(returncode=0, stdout="", stderr="")

            def build_once(
                command: list[str],
                cwd: Path,
                timeout: int,
                environment: dict[str, str],
            ) -> mock.Mock:
                nonlocal attempts
                attempts += 1
                self.assertEqual(cwd, root)
                self.assertEqual(timeout, adapter.timeout_seconds)
                self.assertEqual(command[command.index("--") + 1 :], ["builder"])
                build_tools = json.loads(
                    environment["FIR_VALIDATION_BUILD_TOOLS"]
                )
                self.assertEqual(
                    [
                        (item["kind"], item["name"])
                        for item in build_tools
                    ],
                    [("file-access-recorder", "strace")],
                )
                trace_path = Path(command[command.index("-o") + 1])
                trace_path.write_text(
                    "\n".join(
                        [
                            '100 execve("/usr/bin/builder", ["builder"], 0x0) = 0',
                            f'100 openat(0xffffff9c, "{source}", 0x80000) = 3<{source}>',
                            f'100 openat(0xffffff9c, "{module}", 0x80241) = 4<{module}>',
                        ]
                    )
                    + "\n",
                    encoding="utf-8",
                )
                module.parent.mkdir(parents=True, exist_ok=True)
                module.write_bytes(b"wasm")
                manifest.write_text(
                    json.dumps(
                        {
                            "version": 3,
                            "scope": "reported-loaded",
                            "inputs": [
                                {
                                    "kind": "fixture-source",
                                    "name": "compiler.input",
                                    "path": str(source),
                                }
                            ],
                        }
                    ),
                    encoding="utf-8",
                )
                return completed

            with mock.patch.object(core, "run", side_effect=build_once):
                adapter.build(harness.BuildContext(root, out_dir, False))
            self.assertEqual(attempts, 2)
            self.assertEqual(
                [tool.kind for tool in adapter._built_build_tools],
                ["file-access-recorder"],
            )
            report = json.loads(
                (out_dir / "v8" / "build-file-access.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(report["recorder"]["name"], "strace")
            self.assertTrue(report["accessSetsEqual"])
            self.assertTrue(report["reportedInputsEqual"])
            self.assertEqual(
                [attempt["attempt"] for attempt in report["attempts"]],
                [1, 2],
            )
            for attempt in report["attempts"]:
                self.assertEqual(attempt["accessCount"], 2)
                self.assertEqual(attempt["reportedInputCount"], 1)
                self.assertEqual(
                    attempt["reportedInputs"],
                    [
                        {
                            "backend": "v8",
                            "kind": "fixture-source",
                            "name": "compiler.input",
                            "sha256": harness.sha256_bytes(
                                source.read_bytes()
                            ),
                            "path": str(source),
                            "accesses": ["read"],
                        }
                    ],
                )
            self.assertEqual(
                [
                    artifact.name
                    for artifact in adapter._build_artifacts
                    if artifact.kind == "build-file-access-trace"
                ],
                [
                    "v8/build/file-access.strace",
                    "v8/build-2/file-access.strace",
                ],
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "reported build inputs were not observed",
            ):
                adapter.bind_reported_inputs_to_file_accesses(
                    1,
                    {"attempt": 1},
                    {"/other": ("read",)},
                    (
                        harness.ValidationBuildInput(
                            "v8",
                            "fixture-source",
                            "compiler.input",
                            harness.sha256_bytes(source.read_bytes()),
                            source.read_bytes(),
                            source,
                        ),
                    ),
                )
            adapter.build(harness.BuildContext(root, out_dir, True))
            self.assertEqual(adapter._built_build_tools, ())
            self.assertEqual(adapter._built_build_inputs, ())
            self.assertFalse(
                any(
                    artifact.kind.startswith("build-file-access")
                    for artifact in adapter._build_artifacts
                )
            )

    def test_build_input_manifest_is_strict_and_rejects_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source.olean"
            source.write_bytes(b"olean")

            def manifest(inputs: list[dict], **extra: object) -> bytes:
                return json.dumps(
                    {
                        "version": 3,
                        "scope": "reported-loaded",
                        "inputs": inputs,
                        **extra,
                    }
                ).encode("utf-8")

            valid = {
                "kind": "lean-olean",
                "name": "Example.olean",
                "path": str(source),
            }
            declarations = core.build_input_declarations_from_manifest(
                manifest([valid]), "test build inputs"
            )
            captured = core.validation_build_input_from_file(
                "v8", declarations[0]
            )
            self.assertEqual(captured.sha256, harness.sha256_bytes(b"olean"))

            malformed = (
                {"version": 1, "scope": "reported-loaded", "inputs": [valid]},
                {"version": 3, "scope": "exact", "inputs": [valid]},
                {"version": 3, "scope": "reported-loaded", "inputs": []},
                {
                    "version": 3,
                    "scope": "reported-loaded",
                    "inputs": [valid, valid],
                },
                {
                    "version": 3,
                    "scope": "reported-loaded",
                    "inputs": [
                        valid,
                        {
                            "kind": "other-input",
                            "name": "other",
                            "path": str(source),
                        },
                    ],
                },
                {
                    "version": 3,
                    "scope": "reported-loaded",
                    "inputs": [valid | {"path": "relative.olean"}],
                },
            )
            for value in malformed:
                with self.assertRaises(harness.ValidationError):
                    core.build_input_declarations_from_manifest(
                        json.dumps(value).encode("utf-8"),
                        "test build inputs",
                    )

            leaf_link = root / "leaf.olean"
            leaf_link.symlink_to(source)
            declaration = core.BuildInputDeclaration(
                "lean-olean", "Leaf.olean", leaf_link
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "path contains a symlink"
            ):
                core.validation_build_input_from_file("v8", declaration)

            real_parent = root / "real"
            real_parent.mkdir()
            nested = real_parent / "nested.olean"
            nested.write_bytes(b"nested")
            parent_link = root / "linked"
            parent_link.symlink_to(real_parent, target_is_directory=True)
            declaration = core.BuildInputDeclaration(
                "lean-olean", "Nested.olean", parent_link / "nested.olean"
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "path contains a symlink"
            ):
                core.validation_build_input_from_file("v8", declaration)

    def test_external_build_inputs_fail_closed_and_no_build_omits_claim(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            source = root / "compiler.input"
            source.write_bytes(b"original input")
            raw_manifest = {
                "version": 3,
                "scope": "reported-loaded",
                "inputs": [
                    {
                        "kind": "fixture-source",
                        "name": "compiler.input",
                        "path": str(source),
                    }
                ],
            }
            build_program = (
                "import json,os,pathlib;"
                "path=pathlib.Path(os.environ['FIR_VALIDATION_OUT_DIR'],"
                "'build-inputs.json');"
                "path.parent.mkdir(parents=True,exist_ok=True);"
                f"path.write_text({json.dumps(json.dumps(raw_manifest))})"
            )
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                build_command=[sys.executable, "-c", build_program],
                run_command=[sys.executable, "-c", "raise SystemExit(7)"],
                result_domain="selected",
                build_input_manifest="build-inputs.json",
            )
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            run_context = harness.RunContext(
                root, out_dir, descriptors, ["case"]
            )
            build_context = harness.BuildContext(
                root, out_dir, False, run_context
            )
            adapter.build(build_context)
            self.assertEqual(
                [(item.kind, item.name) for item in adapter._built_build_inputs],
                [
                    ("build-input-manifest", "build-inputs.json"),
                    ("fixture-source", "compiler.input"),
                ],
            )

            source.write_bytes(b"changed before execution")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "build inputs changed between build and execution",
            ):
                adapter.execute(run_context)

            source.write_bytes(b"original input")
            adapter.build(build_context)
            failed = mock.Mock(returncode=7, stdout="", stderr="failed")

            def mutate_input(*args: object, **kwargs: object) -> mock.Mock:
                source.write_bytes(b"changed during execution")
                return failed

            with mock.patch.object(core, "run", side_effect=mutate_input):
                with self.assertRaisesRegex(
                    harness.ValidationError,
                    "build inputs changed during execution",
                ):
                    adapter.execute(run_context)

            adapter.build(
                harness.BuildContext(root, out_dir, True, run_context)
            )
            self.assertEqual(adapter._built_build_inputs, ())

    def test_retained_product_manifest_must_match_matrix_products(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            backend_dir = out_dir / "v8"
            backend_dir.mkdir()
            content = json.dumps(
                {
                    "version": 3,
                    "products": [
                        {"kind": "wasm-module", "path": "module.wasm"}
                    ],
                }
            ).encode("utf-8")
            (backend_dir / "products.json").write_bytes(content)
            product = harness.ValidationProduct(
                "v8",
                "product-manifest",
                "products.json",
                harness.sha256_bytes(content),
            )
            descriptors = [descriptor("case")]
            context = harness.RunContext(
                harness.ROOT, out_dir, descriptors, ["case"]
            )
            harness.write_matrix_artifact(
                context, ["v8"], [], [], products=(product,)
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "disagrees with matrix products"
            ):
                harness.verify_matrix_artifact(out_dir / "matrix.json")

    def test_external_commands_cannot_mutate_canonical_corpus(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            run_context = harness.RunContext(
                root, out_dir, descriptors, ["case"]
            )
            mutate = (
                "import os,pathlib;"
                "pathlib.Path(os.environ['FIR_VALIDATION_CORPUS'])."
                "write_bytes(b'mutated')"
            )
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                build_command=[sys.executable, "-c", mutate],
                run_command=[sys.executable, "-c", mutate],
                result_domain="selected",
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "corpus changed during build"
            ):
                adapter.build(
                    harness.BuildContext(
                        root, out_dir, False, run_context=run_context
                    )
                )

            harness.write_corpus_manifest(out_dir, descriptors)
            adapter.build(
                harness.BuildContext(
                    root, out_dir, True, run_context=run_context
                )
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "corpus changed during execution"
            ):
                adapter.execute(run_context)

    def test_validation_input_hashes_bytes_with_stable_path_labels(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            parent = Path(directory)
            root = parent / "checkout"
            inside = root / "plans" / "matrix.json"
            inside.parent.mkdir(parents=True)
            inside.write_bytes(b"inside\n")
            outside = parent / "v8.json"
            outside.write_bytes(b"outside\n")
            outside_sha256 = harness.sha256_bytes(b"outside\n")

            self.assertEqual(
                harness.validation_input_from_file("validation-plan", inside, root),
                harness.ValidationInput(
                    "validation-plan",
                    "plans/matrix.json",
                    harness.sha256_bytes(b"inside\n"),
                ),
            )
            self.assertEqual(
                harness.validation_input_from_file("adapter-config", outside, root),
                harness.ValidationInput(
                    "adapter-config",
                    f"external/{outside_sha256}/v8.json",
                    outside_sha256,
                ),
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "cannot hash validation input"
            ):
                harness.validation_input_from_file(
                    "adapter-config", parent / "missing.json", root
                )

    def test_adapter_parsing_uses_the_content_bound_for_provenance(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "adapter.json"
            original = json.dumps(
                {
                    "name": "v8",
                    "runCommand": ["node", "run-v8.mjs"],
                    "resultDomain": "selected",
                    "tools": [
                        {"kind": "engine", "name": "node", "command": "node"},
                        {
                            "kind": "runner",
                            "name": "run-v8.mjs",
                            "path": "run-v8.mjs",
                        },
                    ],
                }
            ).encode("utf-8")
            path.write_bytes(original)
            validation_input = harness.validation_input_from_file(
                "adapter-config", path, root
            )
            path.write_text(
                json.dumps(
                    {
                        "name": "talos",
                        "runCommand": ["lake", "exe", "talos"],
                        "resultDomain": "corpus",
                    }
                ),
                encoding="utf-8",
            )
            adapter = harness.external_adapter_from_config(
                path, validation_input.content
            )
            self.assertEqual(adapter.name, "v8")
            self.assertEqual(adapter.run_command, ["node", "run-v8.mjs"])
            self.assertEqual(validation_input.sha256, harness.sha256_bytes(original))

    def test_validation_plan_resolves_configs_and_preserves_pair_order(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_dir = root / "plans"
            plan_dir.mkdir()
            path = plan_dir / "wasm-matrix.json"
            path.write_text(
                json.dumps(
                    {
                        "version": 3,
                        "corpusBackend": "direct-native",
                        "adapterConfigs": [
                            "../adapters/v8.json",
                            "../adapters/talos.json",
                        ],
                        "excludeTags": ["wasm-generation-pending"],
                        "pairs": [
                            {"reference": "native", "candidate": "lcnf"},
                            {"reference": "native", "candidate": "v8"},
                            {"reference": "v8", "candidate": "talos"},
                        ],
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                Path,
                "resolve",
                side_effect=AssertionError(
                    "retained plan parsing consulted the filesystem"
                ),
            ):
                declaration = core.validation_plan_declaration_from_config(
                    Path("relocated/plans/wasm-matrix.json"),
                    path.read_bytes(),
                )
            self.assertEqual(
                declaration.adapter_configs,
                ("../adapters/v8.json", "../adapters/talos.json"),
            )
            self.assertEqual(declaration.corpus_backend, "direct-native")
            self.assertEqual(
                declaration.exclude_tags, ("wasm-generation-pending",)
            )
            self.assertEqual(
                declaration.pairs,
                (
                    ("native", "lcnf"),
                    ("native", "v8"),
                    ("v8", "talos"),
                ),
            )
            plan = harness.validation_plan_from_config(path)
            self.assertEqual(
                plan.adapter_configs,
                (
                    (root / "adapters" / "v8.json").resolve(),
                    (root / "adapters" / "talos.json").resolve(),
                ),
            )
            self.assertEqual(plan.corpus_backend, "direct-native")
            self.assertEqual(plan.exclude_tags, ("wasm-generation-pending",))
            self.assertEqual(
                plan.pairs,
                (
                    ("native", "lcnf"),
                    ("native", "v8"),
                    ("v8", "talos"),
                ),
            )

            value = json.loads(path.read_text(encoding="utf-8"))
            value["pairs"].append(value["pairs"][0])
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "duplicate comparison pairs"
            ):
                harness.validation_plan_from_config(path)

            value["pairs"].pop()
            value["excludeTags"] = ["duplicate", "duplicate"]
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "excludeTags must be sorted and unique"
            ):
                harness.validation_plan_from_config(path)

    def test_retained_plan_rejects_selected_excluded_case(self) -> None:
        plan = config_input(
            "validation-plan",
            "native-v8.json",
            {
                "version": 3,
                "adapterConfigs": [],
                "excludeTags": ["wasm-generation-pending"],
                "pairs": [
                    {"reference": "native", "candidate": "lcnf"}
                ],
            },
        )
        descriptors = [
            descriptor("accepted", tags=["quick"]),
            descriptor(
                "pending", tags=["quick", "wasm-generation-pending"]
            ),
        ]
        core.validate_control_plane_inputs(
            [plan],
            ["native", "lcnf"],
            [("native", "lcnf")],
            [],
            [],
            [],
            descriptors,
            ["accepted"],
        )
        with self.assertRaisesRegex(
            harness.ValidationError, "selected excluded case"
        ):
            core.validate_control_plane_inputs(
                [plan],
                ["native", "lcnf"],
                [("native", "lcnf")],
                [],
                [],
                [],
                descriptors,
                ["pending"],
            )

    def test_control_plane_allows_unused_adapter_without_a_plan(self) -> None:
        inputs = [
            config_input(
                "adapter-config",
                "v8.json",
                fixture_adapter_config("v8"),
            ),
            config_input(
                "adapter-config",
                "unused.json",
                fixture_adapter_config("unused"),
            ),
        ]
        core.validate_control_plane_inputs(
            inputs,
            ["native", "v8"],
            [("native", "v8")],
            [],
            [],
            [],
        )

    def test_checked_native_lcnf_plan_matches_default_matrix(self) -> None:
        plan = harness.validation_plan_from_config(
            harness.ROOT / "validation-plans" / "native-lcnf.json"
        )
        self.assertEqual(plan.adapter_configs, ())
        self.assertEqual(plan.pairs, (("native", "lcnf"),))

    def test_checked_native_v8_scalar_plan_uses_real_engine_adapter(self) -> None:
        adapter_path = (
            harness.ROOT / "validation-adapters" / "v8-scalars.json"
        )
        provider_path = (
            harness.ROOT
            / "validation-providers"
            / "lean-wasm-semantic-scalars.json"
        )
        plan = harness.validation_plan_from_config(
            harness.ROOT
            / "validation-plans"
            / "native-v8-scalars.json"
        )
        self.assertEqual(plan.adapter_configs, (adapter_path.resolve(),))
        self.assertEqual(plan.provider_configs, (provider_path.resolve(),))
        self.assertEqual(plan.pairs, (("native", "v8"),))
        self.assertEqual(
            plan.exclude_tags, ("wasm-generation-pending",)
        )
        adapter = harness.external_adapter_from_config(adapter_path)
        self.assertEqual(adapter.name, "v8")
        self.assertEqual(adapter.build_command, [])
        self.assertEqual(adapter.build_replay_command, [])
        self.assertEqual(
            adapter.run_command,
            [
                "node",
                "scripts/run_validation_v8.mjs",
                "scripts/wasm_semantic_host.mjs",
                "scripts/wasm_validation_externals.mjs",
                "scripts/wasm_validation_case.mjs",
            ],
        )
        self.assertEqual(adapter.product_declarations, ())
        self.assertIsNone(adapter.product_manifest)
        self.assertIsNone(adapter.build_input_manifest)
        self.assertEqual(adapter.build_attempts, 1)
        self.assertEqual(
            adapter.product_provider,
            harness.ProductProviderRequirement(
                "lean-wasm-semantic",
                harness.ProductContract(
                    "wasm",
                    "wasm32",
                    "fir-semantic-runtime-v1",
                    "fir-semantic-abi-v1",
                ),
            ),
        )
        self.assertEqual(adapter.build_tool_declarations, ())
        self.assertIsNone(adapter.build_file_access_recorder)
        self.assertEqual(
            adapter.execution_file_access_recorder,
            harness.ToolDeclaration(
                "execution-file-access-recorder",
                "strace",
                command="strace",
            ),
        )
        self.assertIsNone(adapter.build_input_replay_isolator)
        self.assertEqual(
            [(tool.kind, tool.name) for tool in adapter.tool_declarations],
            [
                ("engine", "node"),
                ("external-registry", "scripts/wasm_validation_externals.mjs"),
                ("runner", "scripts/run_validation_v8.mjs"),
                ("runner-library", "scripts/wasm_validation_case.mjs"),
                ("runtime", "scripts/wasm_semantic_host.mjs"),
            ],
        )

    def test_checked_semantic_wasm_provider_declares_frozen_contract(self) -> None:
        provider_path = (
            harness.ROOT
            / "validation-providers"
            / "lean-wasm-semantic-scalars.json"
        )
        provider = harness.external_product_provider_from_config(provider_path)
        self.assertEqual(provider.name, "lean-wasm-semantic")
        self.assertEqual(
            provider.contract,
            harness.ProductContract(
                "wasm",
                "wasm32",
                "fir-semantic-runtime-v1",
                "fir-semantic-abi-v1",
            ),
        )
        self.assertEqual(provider.bundle_manifest, "products.json")
        self.assertEqual(provider.driver.product_manifest, "products.json")
        self.assertEqual(
            provider.driver.build_input_manifest, "build-inputs.json"
        )
        self.assertEqual(
            provider.driver.build_command,
            ["lake", "lean", "FirValidationWasm.lean"],
        )
        self.assertEqual(
            provider.driver.build_replay_command,
            ["lake", "env", "lean", "FirValidationWasm.lean"],
        )
        self.assertEqual(provider.driver.build_attempts, 2)
        self.assertEqual(
            provider.driver.build_file_access_recorder,
            harness.ToolDeclaration(
                "file-access-recorder", "strace", command="strace"
            ),
        )
        self.assertEqual(
            provider.driver.build_input_replay_isolator,
            harness.ToolDeclaration(
                "build-input-replay-isolator", "bwrap", command="bwrap"
            ),
        )
        self.assertEqual(
            [
                (tool.kind, tool.name)
                for tool in provider.driver.build_tool_declarations
            ],
            [
                ("build-driver", "FirValidationWasm.lean"),
                ("build-launcher", "lake"),
            ],
        )

    def test_checked_native_lcnf_v8_plan_is_complete_triangle(self) -> None:
        adapter_path = (
            harness.ROOT / "validation-adapters" / "v8-scalars.json"
        )
        provider_path = (
            harness.ROOT
            / "validation-providers"
            / "lean-wasm-semantic-scalars.json"
        )
        plan = harness.validation_plan_from_config(
            harness.ROOT
            / "validation-plans"
            / "native-lcnf-v8-scalars.json"
        )
        self.assertEqual(plan.adapter_configs, (adapter_path.resolve(),))
        self.assertEqual(plan.provider_configs, (provider_path.resolve(),))
        self.assertEqual(
            plan.exclude_tags, ("wasm-generation-pending",)
        )
        self.assertEqual(
            plan.pairs,
            (
                ("native", "lcnf"),
                ("native", "v8"),
                ("lcnf", "v8"),
            ),
        )

    def test_provider_consumer_configs_and_plan_are_strict(self) -> None:
        contract = {
            "format": "wasm",
            "target": "wasm32",
            "runtimeFlavor": "fixture",
            "abi": "fixture-v1",
        }
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build_program = (
                "import json,os,pathlib;"
                "root=pathlib.Path(os.environ['FIR_VALIDATION_OUT_DIR']);"
                "(root/'module.wasm').write_bytes(b'fixture-wasm');"
                f"contract=json.loads({json.dumps(json.dumps(contract))});"
                "manifest={'version':3,'contract':contract,'products':["
                "{'kind':'wasm-module','path':'module.wasm'}],'cases':["
                "{'caseId':'case','products':[{'kind':'wasm-module',"
                "'path':'module.wasm'}]}]};"
                "(root/'bundle.json').write_text(json.dumps(manifest))"
            )
            provider_path = root / "provider.json"
            provider_value = {
                "version": 3,
                "name": "fixture-wasm",
                "contract": contract,
                "buildCommand": [
                    Path(sys.executable).name,
                    "-c",
                    build_program,
                ],
                "bundleManifest": "bundle.json",
                "buildTools": [
                    {
                        "kind": "compiler",
                        "name": "python",
                        "command": Path(sys.executable).name,
                    }
                ],
            }
            provider_path.write_text(
                json.dumps(provider_value), encoding="utf-8"
            )
            provider = harness.external_product_provider_from_config(
                provider_path
            )
            self.assertEqual(provider.name, "fixture-wasm")
            self.assertEqual(
                provider.contract,
                harness.ProductContract(
                    "wasm", "wasm32", "fixture", "fixture-v1"
                ),
            )
            self.assertEqual(provider.bundle_manifest, "bundle.json")
            self.assertEqual(provider.driver.product_manifest, "bundle.json")
            out_dir = root / "out"
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            provider_runs = harness.build_product_providers(
                harness.BuildContext(
                    root,
                    out_dir,
                    False,
                    harness.RunContext(
                        root, out_dir, descriptors, ["case"]
                    ),
                ),
                (provider,),
            )
            self.assertEqual(len(provider_runs), 1)
            self.assertEqual(
                [product.name for product in provider_runs[0].bundle.products],
                ["module.wasm"],
            )

            adapter_path = root / "v8.json"
            consumer_program = (
                "import json,os,pathlib;"
                "backend=os.environ['FIR_VALIDATION_BACKEND'];"
                "execution=json.loads(pathlib.Path("
                "os.environ['FIR_VALIDATION_EXECUTION_INPUT']).read_text());"
                "assert execution['selectedCases']==['case'];"
                "bundle=execution['productBundle'];"
                "products=execution['products'];"
                "assert len(products)==1 and products[0]['backend']=='fixture-wasm';"
                "binding=bundle['cases'][0]['products'];"
                "receipt={'provider':bundle['provider'],"
                "'bundleSha256':bundle['bundleSha256'],'products':["
                "{'kind':item['kind'],'name':item['name'],'sha256':item['sha256']}"
                " for item in binding]};"
                "record={'version':3,'caseId':'case','backend':backend,"
                "'diagnostics':[{'key':'validation-product-bundle','value':"
                "json.dumps(receipt,separators=(',',':'),sort_keys=True)}],"
                "'outcome':{'success':{'observation':{'termination':"
                "{'returned':{'value':{'nat':{'value':'42'}}}},'stdout':'',"
                "'stderr':'','effects':[]}}}};"
                "print(json.dumps(record))"
            )
            adapter_value = {
                "name": "v8",
                "runCommand": [
                    Path(sys.executable).name,
                    "-c",
                    consumer_program,
                ],
                "resultDomain": "selected",
                "tools": [
                    {
                        "kind": "engine",
                        "name": "python",
                        "command": Path(sys.executable).name,
                    }
                ],
                "productProvider": {
                    "name": "fixture-wasm",
                    "contract": contract,
                },
            }
            adapter_path.write_text(
                json.dumps(adapter_value), encoding="utf-8"
            )
            adapter = harness.external_adapter_from_config(adapter_path)
            self.assertEqual(
                adapter.product_provider,
                harness.ProductProviderRequirement(
                    "fixture-wasm", provider.contract
                ),
            )
            talos_value = {**adapter_value, "name": "talos"}
            talos_path = root / "talos.json"
            talos_path.write_text(
                json.dumps(talos_value), encoding="utf-8"
            )
            talos = harness.external_adapter_from_config(talos_path)
            consumer_context = harness.RunContext(
                root,
                out_dir,
                descriptors,
                ["case"],
                (
                    harness.validation_input_from_file(
                        "provider-config", provider_path, root
                    ),
                    harness.validation_input_from_file(
                        "adapter-config", adapter_path, root
                    ),
                    harness.validation_input_from_file(
                        "adapter-config", talos_path, root
                    ),
                ),
                product_bundles={
                    "fixture-wasm": provider_runs[0].bundle
                },
            )
            adapter.build(
                harness.BuildContext(
                    root, out_dir, False, consumer_context
                )
            )
            backend_run = adapter.execute(consumer_context)
            self.assertEqual(backend_run.products, [])
            self.assertEqual(
                harness.product_bundle_receipt_findings(
                    backend_run, provider_runs[0].bundle
                ),
                [],
            )
            talos.build(
                harness.BuildContext(
                    root, out_dir, False, consumer_context
                )
            )
            pair_results, findings = harness.validate_matrix(
                consumer_context,
                [(adapter, talos)],
                provider_runs,
            )
            self.assertEqual(findings, [])
            self.assertTrue(pair_results[0].comparisons[0]["equal"])
            provider_matrix = harness.verify_matrix_artifact(
                out_dir / "matrix.json"
            )
            self.assertEqual(
                provider_matrix["providers"], ["fixture-wasm"]
            )
            self.assertEqual(
                [
                    tool["backend"]
                    for tool in provider_matrix["tools"]
                    if tool["kind"] == "compiler"
                ],
                ["fixture-wasm"],
            )

            plan_path = root / "plan.json"
            plan_path.write_text(
                json.dumps(
                    {
                        "version": 3,
                        "providerConfigs": ["provider.json"],
                        "adapterConfigs": ["v8.json"],
                        "pairs": [
                            {"reference": "native", "candidate": "v8"}
                        ],
                    }
                ),
                encoding="utf-8",
            )
            plan = harness.validation_plan_from_config(plan_path)
            self.assertEqual(
                plan.provider_configs, (provider_path.resolve(),)
            )
            self.assertEqual(
                plan.adapter_configs, (adapter_path.resolve(),)
            )

            corpus_consumer = {**adapter_value, "resultDomain": "corpus"}
            with self.assertRaisesRegex(
                harness.ValidationError,
                "productProvider requires resultDomain 'selected'",
            ):
                harness.external_adapter_from_config(
                    adapter_path,
                    json.dumps(corpus_consumer).encode("utf-8"),
                )

            adapter_value["buildCommand"] = [
                sys.executable, "-c", "pass"
            ]
            with self.assertRaisesRegex(
                harness.ValidationError,
                "productProvider cannot be combined",
            ):
                harness.external_adapter_from_config(
                    adapter_path,
                    json.dumps(adapter_value).encode("utf-8"),
                )

            provider_value["runCommand"] = [sys.executable, "-c", "pass"]
            with self.assertRaisesRegex(
                harness.ValidationError,
                "unknown fields: runCommand",
            ):
                harness.external_product_provider_from_config(
                    provider_path,
                    json.dumps(provider_value).encode("utf-8"),
                )

    def test_plan_drives_one_provider_and_two_consumers_through_cli(self) -> None:
        contract = harness.ProductContract(
            "wasm", "wasm32", "fixture-runtime", "fixture-abi"
        )

        class FakeNativeAdapter:
            name = "native"

            def __init__(self) -> None:
                self.build_count = 0

            def build(self, context: harness.BuildContext) -> None:
                self.build_count += 1

        class FakeProvider:
            name = "fixture-wasm"

            def __init__(self) -> None:
                self.build_count = 0

            def build(
                self, context: harness.BuildContext
            ) -> harness.ProductProviderRun:
                self.build_count += 1
                assert context.run_context is not None
                provider_dir = context.out_dir / self.name
                provider_dir.mkdir(parents=True)
                module_content = b"\0asm\x01\0\0\0cli-fixture"
                module_path = provider_dir / "module.wasm"
                module_path.write_bytes(module_content)
                module = harness.ValidationProduct(
                    self.name,
                    "wasm-module",
                    "module.wasm",
                    harness.sha256_bytes(module_content),
                )
                manifest_value = {
                    "version": 3,
                    "contract": contract.to_json(),
                    "products": [
                        {"kind": module.kind, "path": module.name}
                    ],
                    "cases": [
                        {
                            "caseId": "case",
                            "products": [
                                {"kind": module.kind, "path": module.name}
                            ],
                        }
                    ],
                }
                manifest_content = (
                    json.dumps(manifest_value, sort_keys=True) + "\n"
                ).encode("utf-8")
                (provider_dir / "bundle.json").write_bytes(manifest_content)
                manifest = harness.ValidationProduct(
                    self.name,
                    core.RESERVED_PRODUCT_KIND,
                    "bundle.json",
                    harness.sha256_bytes(manifest_content),
                )
                products = tuple(
                    sorted(
                        (manifest, module),
                        key=lambda product: (product.kind, product.name),
                    )
                )
                bundle = core.product_bundle_from_manifest(
                    self.name,
                    contract,
                    manifest_content,
                    products,
                    context.run_context.selected,
                    "CLI fixture provider",
                )
                return harness.ProductProviderRun(
                    self.name, bundle, products=list(products)
                )

        class FakeConsumer:
            def __init__(self, name: str, provider: FakeProvider) -> None:
                self.name = name
                self.provider = provider
                self.product_provider = harness.ProductProviderRequirement(
                    provider.name, contract
                )
                self.build_count = 0
                self.execute_count = 0
                self.audit_count = 0

            def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
                return descriptors

            def build(self, context: harness.BuildContext) -> None:
                self.build_count += 1
                self.assert_provider_built()

            def execute(
                self, context: harness.RunContext
            ) -> harness.BackendRun:
                self.execute_count += 1
                self.assert_provider_built()
                bundle = context.product_bundles[self.provider.name]
                record = success("case", self.name)
                record["diagnostics"] = [
                    {
                        "key": core.PRODUCT_BUNDLE_RECEIPT_DIAGNOSTIC,
                        "value": harness.product_bundle_receipt_value(
                            bundle, "case"
                        ),
                    }
                ]
                return harness.BackendRun(
                    self.name,
                    ["case"],
                    results={"case": record},
                )

            def audit(
                self,
                context: harness.RunContext,
                backend_run: harness.BackendRun,
            ) -> harness.BackendAudit:
                self.audit_count += 1
                return harness.BackendAudit()

            def assert_provider_built(self) -> None:
                if self.provider.build_count != 1:
                    raise AssertionError(
                        "consumer did not observe exactly one provider build"
                    )

        with tempfile.TemporaryDirectory(dir=harness.ROOT) as directory:
            root = Path(directory)
            out_dir = root / "out"
            provider_path = root / "provider.json"
            v8_path = root / "v8.json"
            talos_path = root / "talos.json"
            provider_content = json_bytes(
                fixture_provider_config("fixture-wasm", contract)
            )
            v8_content = json_bytes(
                fixture_consumer_config("v8", "fixture-wasm", contract)
            )
            talos_content = json_bytes(
                fixture_consumer_config(
                    "talos", "fixture-wasm", contract
                )
            )
            provider_path.write_bytes(provider_content)
            v8_path.write_bytes(v8_content)
            talos_path.write_bytes(talos_content)
            plan_path = root / "plan.json"
            plan_path.write_text(
                json.dumps(
                    {
                        "version": 3,
                        "providerConfigs": ["provider.json"],
                        "adapterConfigs": ["v8.json", "talos.json"],
                        "pairs": [
                            {"reference": "v8", "candidate": "talos"}
                        ],
                    }
                ),
                encoding="utf-8",
            )
            native = FakeNativeAdapter()
            provider = FakeProvider()
            v8 = FakeConsumer("v8", provider)
            talos = FakeConsumer("talos", provider)

            def provider_from_config(
                path: Path, content: bytes | None = None
            ) -> FakeProvider:
                self.assertEqual(path, provider_path.resolve())
                self.assertEqual(content, provider_content)
                return provider

            def adapter_from_config(
                path: Path, content: bytes | None = None
            ) -> FakeConsumer:
                self.assertEqual(
                    content,
                    {"v8.json": v8_content, "talos.json": talos_content}[
                        path.name
                    ],
                )
                return {"v8.json": v8, "talos.json": talos}[path.name]

            argv = [
                "validate_interpreters.py",
                "--plan",
                str(plan_path),
                "--out-dir",
                str(out_dir),
            ]
            with (
                mock.patch.object(
                    harness, "BACKEND_ADAPTERS", {"native": native}
                ),
                mock.patch.object(
                    harness,
                    "corpus_manifest",
                    return_value=[descriptor("case")],
                ),
                mock.patch.object(
                    harness,
                    "external_product_provider_from_config",
                    side_effect=provider_from_config,
                ),
                mock.patch.object(
                    harness,
                    "external_adapter_from_config",
                    side_effect=adapter_from_config,
                ),
                mock.patch.object(sys, "argv", argv),
                contextlib.redirect_stdout(io.StringIO()) as stdout,
            ):
                self.assertEqual(harness.main(), 0)

            self.assertIn("v8 == talos", stdout.getvalue())
            self.assertEqual(native.build_count, 1)
            self.assertEqual(provider.build_count, 1)
            for consumer in (v8, talos):
                self.assertEqual(consumer.build_count, 1)
                self.assertEqual(consumer.execute_count, 1)
                self.assertEqual(consumer.audit_count, 1)

            matrix_path = out_dir / "matrix.json"
            matrix_content = matrix_path.read_bytes()
            matrix = json.loads(matrix_content)
            self.assertEqual(matrix["providers"], [provider.name])
            self.assertEqual(matrix["backends"], ["v8", "talos"])
            self.assertEqual(
                [item["kind"] for item in matrix["inputs"]],
                [
                    "corpus",
                    "validation-plan",
                    "provider-config",
                    "adapter-config",
                    "adapter-config",
                ],
            )
            self.assertEqual(matrix["summary"]["comparisonCount"], 1)
            self.assertEqual(matrix["summary"]["productReceiptCount"], 2)
            self.assertEqual(
                [
                    (receipt["backend"], receipt["caseId"])
                    for receipt in matrix["productReceipts"]
                ],
                [("talos", "case"), ("v8", "case")],
            )
            evidence_path = harness.validation_evidence_manifest_path(
                out_dir,
                matrix["identity"]["run"],
                harness.sha256_bytes(matrix_content),
            )
            shutil.rmtree(out_dir / provider.name)
            harness.verify_evidence_manifest(evidence_path)
            relocated = root / "relocated-report"
            shutil.copytree(out_dir, relocated)
            relocated_evidence = (
                relocated / evidence_path.relative_to(out_dir)
            )
            original_cwd = Path.cwd()
            try:
                os.chdir(root)
                harness.verify_evidence_manifest(relocated_evidence)
            finally:
                os.chdir(original_cwd)

            def rewrite_control_input(
                base: dict,
                kind: str,
                filename: str,
                value: dict,
            ) -> dict:
                tampered = json.loads(json.dumps(base))
                item = next(
                    candidate
                    for candidate in tampered["inputs"]
                    if candidate["kind"] == kind
                    and Path(candidate["name"]).name == filename
                )
                content = json_bytes(value)
                digest = harness.sha256_bytes(content)
                item["sha256"] = digest
                item["artifact"] = harness.retain_evidence_blob(
                    out_dir, "inputs", digest, content
                )
                run_value = {
                    "version": 3,
                    "selectionSha256": tampered["identity"]["selection"],
                    "backends": tampered["backends"],
                    "pairs": [
                        {
                            "reference": pair["reference"],
                            "candidate": pair["candidate"],
                        }
                        for pair in tampered["pairs"]
                    ],
                    "inputs": [
                        {
                            key: entry[key]
                            for key in ("kind", "name", "sha256")
                        }
                        for entry in tampered["inputs"]
                    ],
                    "products": [
                        {
                            key: entry[key]
                            for key in (
                                "backend",
                                "kind",
                                "name",
                                "sha256",
                            )
                        }
                        for entry in tampered["products"]
                    ],
                    "tools": [
                        {
                            key: entry[key]
                            for key in (
                                "backend",
                                "kind",
                                "name",
                                "sha256",
                            )
                        }
                        for entry in tampered["tools"]
                    ],
                    "buildInputs": [
                        {
                            key: entry[key]
                            for key in (
                                "backend",
                                "kind",
                                "name",
                                "sha256",
                            )
                        }
                        for entry in tampered["buildInputs"]
                    ],
                    "productBundles": tampered["productBundles"],
                    "productConsumers": tampered["productConsumers"],
                    "productReceipts": tampered["productReceipts"],
                }
                tampered["identity"]["run"] = (
                    harness.canonical_json_sha256(run_value)
                )
                matrix_path.write_text(
                    json.dumps(tampered, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8",
                )
                return tampered

            provider_contract_drift = json.loads(
                provider_content.decode("utf-8")
            )
            provider_contract_drift["contract"]["abi"] = "fixture-abi-drift"
            provider_manifest_drift = json.loads(
                provider_content.decode("utf-8")
            )
            provider_manifest_drift["bundleManifest"] = "other.json"
            consumer_provider_drift = json.loads(v8_content.decode("utf-8"))
            consumer_provider_drift["productProvider"]["name"] = "other-provider"
            consumer_contract_drift = json.loads(v8_content.decode("utf-8"))
            consumer_contract_drift["productProvider"]["contract"]["abi"] = (
                "fixture-abi-drift"
            )
            plan_pair_drift = json.loads(plan_path.read_text(encoding="utf-8"))
            plan_pair_drift["pairs"] = [
                {"reference": "talos", "candidate": "v8"}
            ]
            drift_cases = [
                (
                    "provider contract",
                    "provider-config",
                    "provider.json",
                    provider_contract_drift,
                    "provider config contract disagrees with bundle",
                ),
                (
                    "provider manifest",
                    "provider-config",
                    "provider.json",
                    provider_manifest_drift,
                    "provider config bundle manifest disagrees with products",
                ),
                (
                    "consumer provider",
                    "adapter-config",
                    "v8.json",
                    consumer_provider_drift,
                    "adapter config product provider disagrees with matrix consumer",
                ),
                (
                    "consumer contract",
                    "adapter-config",
                    "v8.json",
                    consumer_contract_drift,
                    "adapter config product provider disagrees with matrix consumer",
                ),
                (
                    "plan pair",
                    "validation-plan",
                    "plan.json",
                    plan_pair_drift,
                    "validation plan pairs disagree with matrix",
                ),
            ]
            for label, kind, filename, value, message in drift_cases:
                with self.subTest(control_plane_drift=label):
                    rewrite_control_input(matrix, kind, filename, value)
                    with self.assertRaisesRegex(
                        harness.ValidationError, message
                    ):
                        harness.verify_matrix_artifact(matrix_path)
            matrix_path.write_bytes(matrix_content)

    def test_plan_drives_external_adapter_through_cli_and_matrix(self) -> None:
        native_value = {"value": 42}

        class FakeNativeAdapter:
            name = "native"

            def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
                return descriptors

            def build(self, context: harness.BuildContext) -> None:
                pass

            def execute(self, context: harness.RunContext) -> harness.BackendRun:
                return harness.BackendRun(
                    self.name,
                    list(context.selected),
                    {
                        "case": success(
                            "case", self.name, native_value["value"]
                        )
                    },
                )

            def audit(
                self,
                context: harness.RunContext,
                backend_run: harness.BackendRun,
            ) -> harness.BackendAudit:
                return harness.BackendAudit()

        with tempfile.TemporaryDirectory(dir=harness.ROOT) as directory:
            root = Path(directory)
            out_dir = root / "out"
            product_path = out_dir / "v8" / "modules" / "validation.wasm"
            product_path.parent.mkdir(parents=True)
            product_bytes = b"\0asm\x01\0\0\0test-product"
            product_path.write_bytes(b"stale-product")
            adapter_path = root / "v8.json"
            runner_path = root / "runner.py"
            material_path = root / "compiler.input"
            material_bytes = b"exact compiler input"
            material_path.write_bytes(material_bytes)
            isolator_path = root / "fake-bwrap"
            isolator_path.write_text(
                "#!/usr/bin/env python3\n"
                "import fcntl,json,os,pathlib,subprocess,sys\n"
                "args=sys.argv[1:]\n"
                "environment={}\n"
                "status_fd=None\n"
                "cwd=None\n"
                "payload=None\n"
                "pending_mode=None\n"
                "index=0\n"
                "while index < len(args):\n"
                " arg=args[index]\n"
                " if arg == '--':\n"
                "  payload=args[index+1:]\n"
                "  break\n"
                " if arg == '--setenv':\n"
                "  environment[args[index+1]]=args[index+2]\n"
                "  index+=3\n"
                " elif arg == '--json-status-fd':\n"
                "  status_fd=int(args[index+1])\n"
                "  index+=2\n"
                " elif arg == '--chdir':\n"
                "  cwd=args[index+1]\n"
                "  index+=2\n"
                " elif arg == '--perms':\n"
                "  pending_mode=int(args[index+1],8)\n"
                "  index+=2\n"
                " elif arg == '--ro-bind-data':\n"
                "  descriptor=int(args[index+1])\n"
                "  target=pathlib.Path(args[index+2])\n"
                "  assert pending_mode in (0o444,0o555)\n"
                "  assert os.fstat(descriptor).st_mode & 0o777 == pending_mode\n"
                "  assert fcntl.fcntl(descriptor,fcntl.F_GET_SEALS) == "
                "(fcntl.F_SEAL_WRITE|fcntl.F_SEAL_GROW|"
                "fcntl.F_SEAL_SHRINK|fcntl.F_SEAL_SEAL)\n"
                "  assert pathlib.Path(f'/proc/self/fd/{descriptor}').read_bytes()"
                " == target.read_bytes()\n"
                "  pending_mode=None\n"
                "  index+=3\n"
                " elif arg in ('--ro-bind','--bind'):\n"
                "  index+=3\n"
                " elif arg in ('--proc','--dev','--tmpfs','--dir',"
                "'--cap-drop','--hostname'):\n"
                "  index+=2\n"
                " else:\n"
                "  index+=1\n"
                "assert status_fd is not None and cwd is not None and payload\n"
                "namespace={key:os.getpid() for key in "
                "('child-pid','cgroup-namespace','ipc-namespace',"
                "'mnt-namespace','net-namespace','pid-namespace',"
                "'uts-namespace')}\n"
                "os.write(status_fd,(json.dumps(namespace)+'\\n').encode())\n"
                "completed=subprocess.run(payload,cwd=cwd,env=environment,"
                "text=True,capture_output=True)\n"
                "os.write(status_fd,(json.dumps({'exit-code':completed.returncode})"
                "+'\\n').encode())\n"
                "sys.stdout.write(completed.stdout)\n"
                "sys.stderr.write(completed.stderr)\n"
                "raise SystemExit(completed.returncode)\n",
                encoding="utf-8",
            )
            isolator_path.chmod(0o755)
            isolator_sha256 = harness.sha256_bytes(
                isolator_path.read_bytes()
            )
            recorder_path = root / "fake-strace"
            recorder_path.write_text(
                "#!/usr/bin/env python3\n"
                "import json,os,pathlib,subprocess,sys\n"
                "args=sys.argv[1:]\n"
                "trace=pathlib.Path(args[args.index('-o')+1])\n"
                "command=args[args.index('--')+1:]\n"
                "passed=[]\n"
                "for index,arg in enumerate(command[:-1]):\n"
                " if arg in ('--ro-bind-data','--json-status-fd'):\n"
                "  passed.append(int(command[index+1]))\n"
                "completed=subprocess.run(command,text=True,capture_output=True,"
                "pass_fds=tuple(passed))\n"
                "executable=str(pathlib.Path(command[0]).resolve())\n"
                "lines=[f'{os.getpid()} execve({json.dumps(executable)}, [], 0x0) = 0']\n"
                "if '--' in command:\n"
                " payload=command[command.index('--')+1:]\n"
                " payload_executable=str(pathlib.Path(payload[0]).resolve())\n"
                " lines.append(f'{os.getpid()} execve({json.dumps(payload_executable)}, [], 0x0) = 0')\n"
                "if completed.returncode == 0:\n"
                " manifest=pathlib.Path(os.environ['FIR_VALIDATION_OUT_DIR'],'build-inputs.json')\n"
                " for item in json.loads(manifest.read_text())['inputs']:\n"
                "  path=item['path']\n"
                "  lines.append(f'{os.getpid()} openat(-100</>, {json.dumps(path)}, 0x80000) = 3<{path}>')\n"
                "trace.write_text('\\n'.join(lines)+'\\n')\n"
                "sys.stdout.write(completed.stdout)\n"
                "sys.stderr.write(completed.stderr)\n"
                "raise SystemExit(completed.returncode)\n",
                encoding="utf-8",
            )
            recorder_path.chmod(0o755)
            recorder_sha256 = harness.sha256_bytes(
                recorder_path.read_bytes()
            )
            product_sha256 = harness.sha256_bytes(product_bytes)
            build_program = (
                "import json,os,pathlib;"
                "assert json.loads(os.environ['FIR_VALIDATION_CASES'])==['case'];"
                "build_tools=json.loads(os.environ['FIR_VALIDATION_BUILD_TOOLS']);"
                "assert [(tool['kind'],tool['name']) for tool in build_tools]"
                "==[('build-input-replay-isolator','fake-bwrap'),"
                "('build-launcher','python-build'),"
                "('file-access-recorder','fake-strace')];"
                "assert pathlib.Path(os.environ['FIR_VALIDATION_CORPUS']).is_file();"
                f"assert pathlib.Path({str(material_path)!r}).read_bytes()=={material_bytes!r};"
                "path=pathlib.Path(os.environ['FIR_VALIDATION_OUT_DIR'],"
                "'modules','validation.wasm');"
                "path.parent.mkdir(parents=True,exist_ok=True);"
                f"path.write_bytes({product_bytes!r});"
                "closure={'version':3,'scope':'reported-loaded','inputs':["
                "{'kind':'fixture-source','name':'compiler.input','path':"
                f"{str(material_path)!r}" "}]};"
                "pathlib.Path(os.environ['FIR_VALIDATION_OUT_DIR'],"
                "'build-inputs.json').write_text(json.dumps(closure))"
            )
            program = (
                "import hashlib,json,os,pathlib;"
                "execution=json.loads(pathlib.Path("
                "os.environ['FIR_VALIDATION_EXECUTION_INPUT']).read_text());"
                "assert execution['selectedCases']==['case'];"
                "products=execution['products'];"
                "tools=json.loads(os.environ['FIR_VALIDATION_TOOLS']);"
                "assert len(products)==1;"
                "assert [tool['kind'] for tool in tools]==['engine','runner'];"
                "assert all(hashlib.sha256(pathlib.Path(tool['path']).read_bytes()).hexdigest()"
                "==tool['sha256'] for tool in tools);"
                f"assert products[0]['sha256']=={product_sha256!r};"
                f"assert pathlib.Path(products[0]['path']).read_bytes()=={product_bytes!r};"
                f"record=json.loads({json.dumps(json.dumps(success('case', 'v8')))});"
                "receipt=[{'kind':product['kind'],'name':product['name'],"
                "'sha256':hashlib.sha256(pathlib.Path(product['path']).read_bytes()).hexdigest()}"
                " for product in products];"
                "record['diagnostics']=[{'key':'validation-products',"
                "'value':json.dumps(receipt,separators=(',',':'),sort_keys=True)}];"
                "print(json.dumps(record))"
            )
            runner_path.write_text(program, encoding="utf-8")
            runner_sha256 = harness.sha256_bytes(runner_path.read_bytes())
            engine_command = Path(sys.executable).name
            engine_path_text = shutil.which(engine_command)
            self.assertIsNotNone(engine_path_text)
            assert engine_path_text is not None
            engine_path = Path(engine_path_text).resolve()
            engine_sha256 = harness.sha256_bytes(engine_path.read_bytes())
            adapter_path.write_text(
                json.dumps(
                    {
                        "name": "v8",
                        "buildCommand": [
                            engine_command,
                            "-c",
                            build_program,
                        ],
                        "buildReplayCommand": [
                            engine_command,
                            "-c",
                            build_program,
                        ],
                        "buildAttempts": 2,
                        "buildFileAccessRecorder": {
                            "kind": "file-access-recorder",
                            "name": "fake-strace",
                            "command": "fake-strace",
                        },
                        "buildInputReplay": {
                            "kind": "build-input-replay-isolator",
                            "name": "fake-bwrap",
                            "command": "fake-bwrap",
                        },
                        "runCommand": [engine_command, str(runner_path)],
                        "resultDomain": "selected",
                        "products": [
                            {
                                "kind": "wasm-module",
                                "path": "modules/validation.wasm",
                            }
                        ],
                        "buildInputManifest": "build-inputs.json",
                        "buildTools": [
                            {
                                "kind": "build-launcher",
                                "name": "python-build",
                                "command": engine_command,
                            }
                        ],
                        "tools": [
                            {
                                "kind": "runner",
                                "name": "runner.py",
                                "path": "runner.py",
                            },
                            {
                                "kind": "engine",
                                "name": "python",
                                "command": engine_command,
                            },
                        ],
                    }
                ),
                encoding="utf-8",
            )
            plan_path = root / "matrix.json"
            plan_path.write_text(
                json.dumps(
                    {
                        "version": 3,
                        "adapterConfigs": ["v8.json"],
                        "pairs": [
                            {"reference": "native", "candidate": "v8"}
                        ],
                    }
                ),
                encoding="utf-8",
            )
            argv = [
                "validate_interpreters.py",
                "--plan",
                str(plan_path),
                "--out-dir",
                str(out_dir),
            ]
            with (
                mock.patch.object(
                    harness, "BACKEND_ADAPTERS", {"native": FakeNativeAdapter()}
                ),
                mock.patch.object(
                    harness, "corpus_manifest", return_value=[descriptor("case")]
                ),
                mock.patch.dict(
                    os.environ,
                    {"PATH": f"{root}{os.pathsep}{os.environ['PATH']}"},
                ),
                mock.patch.object(sys, "argv", argv),
                contextlib.redirect_stdout(io.StringIO()) as stdout,
            ):
                self.assertEqual(harness.main(), 0)
            self.assertIn("native == v8", stdout.getvalue())
            matrix = json.loads(
                (out_dir / "matrix.json").read_text(encoding="utf-8")
            )
            self.assertEqual(matrix["backends"], ["native", "v8"])
            self.assertEqual(matrix["summary"]["equalComparisonCount"], 1)
            self.assertEqual(
                [item["kind"] for item in matrix["inputs"]],
                ["corpus", "validation-plan", "adapter-config"],
            )
            plan_sha256 = harness.sha256_bytes(plan_path.read_bytes())
            adapter_sha256 = harness.sha256_bytes(adapter_path.read_bytes())
            self.assertEqual(
                [item["name"] for item in matrix["inputs"]],
                [
                    "corpus.json",
                    f"{root.name}/matrix.json",
                    f"{root.name}/v8.json",
                ],
            )
            self.assertEqual(
                [item["sha256"] for item in matrix["inputs"]],
                [
                    harness.sha256_bytes((out_dir / "corpus.json").read_bytes()),
                    plan_sha256,
                    adapter_sha256,
                ],
            )
            for item in matrix["inputs"]:
                self.assertEqual(
                    item["artifact"], f"evidence/inputs/{item['sha256']}"
                )
            self.assertEqual(
                matrix["products"],
                [
                    {
                        "backend": "v8",
                        "kind": "wasm-module",
                        "name": "modules/validation.wasm",
                        "sha256": product_sha256,
                        "artifact": f"evidence/products/{product_sha256}",
                    }
                ],
            )
            self.assertEqual(matrix["summary"]["productCount"], 1)
            self.assertEqual(
                matrix["tools"],
                [
                    {
                        "backend": "v8",
                        "kind": "build-input-replay-isolator",
                        "name": "fake-bwrap",
                        "sha256": isolator_sha256,
                        "artifact": f"evidence/tools/{isolator_sha256}",
                    },
                    {
                        "backend": "v8",
                        "kind": "build-launcher",
                        "name": "python-build",
                        "sha256": engine_sha256,
                        "artifact": f"evidence/tools/{engine_sha256}",
                    },
                    {
                        "backend": "v8",
                        "kind": "engine",
                        "name": "python",
                        "sha256": engine_sha256,
                        "artifact": f"evidence/tools/{engine_sha256}",
                    },
                    {
                        "backend": "v8",
                        "kind": "file-access-recorder",
                        "name": "fake-strace",
                        "sha256": recorder_sha256,
                        "artifact": f"evidence/tools/{recorder_sha256}",
                    },
                    {
                        "backend": "v8",
                        "kind": "runner",
                        "name": "runner.py",
                        "sha256": runner_sha256,
                        "artifact": f"evidence/tools/{runner_sha256}",
                    },
                ],
            )
            self.assertEqual(matrix["summary"]["toolCount"], 5)
            self.assertEqual(matrix["summary"]["buildInputCount"], 2)
            self.assertEqual(
                [
                    (item["kind"], item["name"])
                    for item in matrix["buildInputs"]
                ],
                [
                    ("build-input-manifest", "build-inputs.json"),
                    ("fixture-source", "compiler.input"),
                ],
            )
            material_sha256 = harness.sha256_bytes(material_bytes)
            self.assertEqual(
                matrix["buildInputs"][1],
                {
                    "backend": "v8",
                    "kind": "fixture-source",
                    "name": "compiler.input",
                    "sha256": material_sha256,
                    "artifact": f"evidence/build-inputs/{material_sha256}",
                },
            )
            self.assertEqual(matrix["summary"]["artifactCount"], 19)
            self.assertEqual(
                [(item["kind"], item["name"]) for item in matrix["artifacts"]],
                [
                    ("backend-result", "case/native/result.json"),
                    ("backend-result", "case/v8/result.json"),
                    ("build-determinism", "v8/build-determinism.json"),
                    ("build-file-access", "v8/build-file-access.json"),
                    (
                        "build-file-access-trace",
                        "v8/build-2/file-access.strace",
                    ),
                    (
                        "build-file-access-trace",
                        "v8/build/file-access.strace",
                    ),
                    ("build-input-replay", "v8/build-input-replay.json"),
                    (
                        "build-input-replay-manifest",
                        "v8/build-input-replay/build-input-manifest.json",
                    ),
                    (
                        "build-input-replay-status",
                        "v8/build-input-replay/sandbox-status.jsonl",
                    ),
                    (
                        "build-input-replay-trace",
                        "v8/build-input-replay/file-access.strace",
                    ),
                    ("execution-input", "v8/execution-input.json"),
                    ("process-stderr", "v8/build-2/stderr.log"),
                    (
                        "process-stderr",
                        "v8/build-input-replay/stderr.log",
                    ),
                    ("process-stderr", "v8/build/stderr.log"),
                    ("process-stderr", "v8/stderr.log"),
                    ("process-stdout", "v8/build-2/stdout.jsonl"),
                    (
                        "process-stdout",
                        "v8/build-input-replay/stdout.jsonl",
                    ),
                    ("process-stdout", "v8/build/stdout.jsonl"),
                    ("process-stdout", "v8/stdout.jsonl"),
                ],
            )
            for item in matrix["artifacts"]:
                self.assertEqual(
                    item["artifact"], f"evidence/artifacts/{item['sha256']}"
                )
            determinism_item = next(
                item
                for item in matrix["artifacts"]
                if item["kind"] == "build-determinism"
            )
            determinism = json.loads(
                (out_dir / determinism_item["artifact"]).read_text(
                    encoding="utf-8"
                )
            )
            self.assertTrue(determinism["equal"])
            self.assertEqual(
                [attempt["attempt"] for attempt in determinism["attempts"]],
                [1, 2],
            )
            self.assertTrue(
                (out_dir / "comparisons" / "native--v8.json").is_file()
            )
            matrix_path = out_dir / "matrix.json"
            original_matrix_bytes = matrix_path.read_bytes()
            evidence_path = harness.validation_evidence_manifest_path(
                out_dir,
                matrix["identity"]["run"],
                harness.sha256_bytes(original_matrix_bytes),
            )
            evidence = harness.verify_evidence_manifest(evidence_path)
            receipt_path = (
                out_dir / core.VALIDATION_EVIDENCE_RECEIPT_NAME
            )
            receipt = json.loads(receipt_path.read_bytes())
            self.assertEqual(
                receipt["source"],
                {
                    "runSha256": matrix["identity"]["run"],
                    "evidenceSha256": evidence["identity"]["evidence"],
                    "matrixSha256": harness.sha256_bytes(
                        original_matrix_bytes
                    ),
                },
            )
            self.assertEqual(
                receipt["manifest"],
                evidence_path.relative_to(out_dir).as_posix(),
            )
            self.assertEqual(
                core.verify_evidence_receipt(receipt_path).manifest_path,
                evidence_path.resolve(),
            )
            tampered = json.loads(json.dumps(receipt))
            tampered["source"]["matrixSha256"] = "f" * 64
            provisional = dict(tampered)
            provisional.pop("identity")
            tampered["identity"]["receipt"] = (
                harness.canonical_json_sha256(provisional)
            )
            receipt_path.write_bytes(json_bytes(tampered))
            with self.assertRaisesRegex(
                harness.ValidationError,
                "disagrees with its immutable source",
            ):
                core.verify_evidence_receipt(receipt_path)
            core.write_evidence_receipt(out_dir, evidence_path)
            escaping = json.loads(receipt_path.read_bytes())
            escaping["manifest"] = "../outside.json"
            provisional = dict(escaping)
            provisional.pop("identity")
            escaping["identity"]["receipt"] = (
                harness.canonical_json_sha256(provisional)
            )
            receipt_path.write_bytes(json_bytes(escaping))
            with self.assertRaisesRegex(
                harness.ValidationError,
                "normalized relative POSIX path",
            ):
                core.verify_evidence_receipt(receipt_path)
            core.write_evidence_receipt(out_dir, evidence_path)
            receipt_link = out_dir / "receipt-link.json"
            receipt_link.symlink_to(receipt_path.name)
            with self.assertRaisesRegex(
                harness.ValidationError, "must not be a symlink"
            ):
                core.verify_evidence_receipt(receipt_link)
            self.assertEqual(
                (out_dir / evidence["matrix"]["artifact"]).read_bytes(),
                original_matrix_bytes,
            )
            moved_report = root / "moved-report"
            shutil.copytree(out_dir, moved_report)
            moved_evidence = moved_report / evidence_path.relative_to(out_dir)
            self.assertEqual(
                harness.verify_evidence_manifest(moved_evidence)["identity"],
                evidence["identity"],
            )
            moved_receipt = moved_report / receipt_path.relative_to(out_dir)
            self.assertEqual(
                core.verify_evidence_receipt(moved_receipt).manifest_path,
                moved_evidence.resolve(),
            )
            same_comparison = core.compare_verified_evidence(
                core.verify_evidence_snapshot(evidence_path),
                core.verify_evidence_snapshot(moved_evidence),
            )
            self.assertFalse(any(same_comparison["classification"].values()))
            self.assertEqual(
                same_comparison["equivalence"],
                {"portable": True, "exact": True},
            )
            self.assertEqual(same_comparison["semanticResults"], [])
            self.assertIn(
                "contract same",
                "\n".join(core.render_evidence_comparison(same_comparison)),
            )

            diagnostic_matrix = json.loads(json.dumps(matrix))
            diagnostic_item = next(
                item
                for item in diagnostic_matrix["artifacts"]
                if item["kind"] == "process-stderr"
                and item["name"] == "v8/stderr.log"
            )
            diagnostic_content = (
                out_dir / diagnostic_item["artifact"]
            ).read_bytes() + b"ASLR-only raw address: 0x12345678\n"
            diagnostic_sha256 = harness.sha256_bytes(diagnostic_content)
            diagnostic_item.update(
                {
                    "sha256": diagnostic_sha256,
                    "artifact": core.retain_evidence_blob(
                        out_dir,
                        "artifacts",
                        diagnostic_sha256,
                        diagnostic_content,
                    ),
                }
            )
            diagnostic_matrix_content = (
                json.dumps(diagnostic_matrix, indent=2, sort_keys=True) + "\n"
            ).encode("utf-8")
            diagnostic_evidence_path = core.write_evidence_manifest(
                out_dir,
                diagnostic_matrix_content,
                matrix["identity"]["run"],
            )
            diagnostic_comparison = core.compare_verified_evidence(
                core.verify_evidence_snapshot(evidence_path),
                core.verify_evidence_snapshot(diagnostic_evidence_path),
            )
            self.assertTrue(
                diagnostic_comparison["classification"]["evidenceChanged"]
            )
            self.assertTrue(
                diagnostic_comparison["classification"]["artifactsChanged"]
            )
            self.assertFalse(
                diagnostic_comparison["classification"][
                    "portableClaimChanged"
                ]
            )
            self.assertEqual(
                diagnostic_comparison["equivalence"],
                {"portable": True, "exact": False},
            )
            self.assertTrue(
                core.evidence_comparison_equivalent(
                    diagnostic_comparison, "portable"
                )
            )
            self.assertFalse(
                core.evidence_comparison_equivalent(
                    diagnostic_comparison, "exact"
                )
            )
            self.assertIn(
                "equivalence: portable same, exact changed",
                "\n".join(
                    core.render_evidence_comparison(diagnostic_comparison)
                ),
            )
            for level, expected_status in (("portable", 0), ("exact", 1)):
                with (
                    mock.patch.object(
                        sys,
                        "argv",
                        [
                            "validate_interpreters.py",
                            "--compare-evidence",
                            str(evidence_path),
                            str(diagnostic_evidence_path),
                            "--require-evidence-equivalence",
                            level,
                        ],
                    ),
                    contextlib.redirect_stdout(io.StringIO()),
                ):
                    self.assertEqual(harness.main(), expected_status)

            native_value["value"] = 43
            with (
                mock.patch.object(
                    harness,
                    "BACKEND_ADAPTERS",
                    {"native": FakeNativeAdapter()},
                ),
                mock.patch.object(
                    harness,
                    "corpus_manifest",
                    return_value=[descriptor("case")],
                ),
                mock.patch.dict(
                    os.environ,
                    {"PATH": f"{root}{os.pathsep}{os.environ['PATH']}"},
                ),
                mock.patch.object(sys, "argv", argv),
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(io.StringIO()),
            ):
                self.assertEqual(harness.main(), 1)
            changed_matrix_bytes = matrix_path.read_bytes()
            changed_matrix = json.loads(changed_matrix_bytes)
            changed_evidence_path = harness.validation_evidence_manifest_path(
                out_dir,
                changed_matrix["identity"]["run"],
                harness.sha256_bytes(changed_matrix_bytes),
            )
            semantic_comparison = core.compare_verified_evidence(
                core.verify_evidence_snapshot(evidence_path),
                core.verify_evidence_snapshot(changed_evidence_path),
            )
            self.assertFalse(
                semantic_comparison["classification"]["runChanged"]
            )
            self.assertFalse(
                semantic_comparison["classification"]["contractChanged"]
            )
            self.assertTrue(
                semantic_comparison["classification"][
                    "semanticResultsChanged"
                ]
            )
            self.assertTrue(
                semantic_comparison["classification"][
                    "semanticObservationsChanged"
                ]
            )
            self.assertTrue(
                semantic_comparison["classification"]["coverageClaimChanged"]
            )
            self.assertTrue(
                semantic_comparison["classification"]["findingsChanged"]
            )
            self.assertTrue(
                semantic_comparison["classification"]["portableClaimChanged"]
            )
            self.assertEqual(
                semantic_comparison["equivalence"],
                {"portable": False, "exact": False},
            )
            self.assertEqual(
                [
                    (
                        item["backend"],
                        item["caseId"],
                        item["change"],
                    )
                    for item in semantic_comparison["semanticResults"]
                ],
                [("native", "case", "changed")],
            )
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "validate_interpreters.py",
                        "--compare-evidence",
                        str(evidence_path),
                        str(changed_evidence_path),
                        "--json",
                    ],
                ),
                contextlib.redirect_stdout(io.StringIO()) as comparison_stdout,
            ):
                self.assertEqual(harness.main(), 0)
            cli_comparison = json.loads(comparison_stdout.getvalue())
            self.assertEqual(
                cli_comparison["classification"],
                semantic_comparison["classification"],
            )
            self.assertEqual(
                cli_comparison["equivalence"],
                semantic_comparison["equivalence"],
            )
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "validate_interpreters.py",
                        "--compare-evidence",
                        str(evidence_path),
                        str(changed_evidence_path),
                        "--require-evidence-equivalence",
                        "portable",
                    ],
                ),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(harness.main(), 1)
            matrix_path.write_bytes(original_matrix_bytes)
            native_value["value"] = 42

            original_plan_bytes = plan_path.read_bytes()
            reversed_plan = json.loads(original_plan_bytes)
            reversed_plan["pairs"] = [
                {"reference": "v8", "candidate": "native"}
            ]
            plan_path.write_text(
                json.dumps(reversed_plan), encoding="utf-8"
            )
            with (
                mock.patch.object(
                    harness,
                    "BACKEND_ADAPTERS",
                    {"native": FakeNativeAdapter()},
                ),
                mock.patch.object(
                    harness,
                    "corpus_manifest",
                    return_value=[descriptor("case")],
                ),
                mock.patch.dict(
                    os.environ,
                    {"PATH": f"{root}{os.pathsep}{os.environ['PATH']}"},
                ),
                mock.patch.object(sys, "argv", argv),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(harness.main(), 0)
            contract_matrix_bytes = matrix_path.read_bytes()
            contract_matrix = json.loads(contract_matrix_bytes)
            contract_evidence_path = harness.validation_evidence_manifest_path(
                out_dir,
                contract_matrix["identity"]["run"],
                harness.sha256_bytes(contract_matrix_bytes),
            )
            contract_comparison = core.compare_verified_evidence(
                core.verify_evidence_snapshot(evidence_path),
                core.verify_evidence_snapshot(contract_evidence_path),
            )
            self.assertTrue(
                contract_comparison["classification"]["runChanged"]
            )
            self.assertTrue(
                contract_comparison["classification"]["contractChanged"]
            )
            self.assertFalse(
                contract_comparison["classification"][
                    "semanticResultsChanged"
                ]
            )
            self.assertTrue(contract_comparison["pairGraph"]["changed"])
            self.assertEqual(
                contract_comparison["summary"]["inventoryCounts"]["inputs"],
                {"added": 0, "removed": 0, "changed": 1},
            )
            self.assertIn(
                "pairGraph: +1 -1",
                "\n".join(
                    core.render_evidence_comparison(contract_comparison)
                ),
            )
            plan_path.write_bytes(original_plan_bytes)
            matrix_path.write_bytes(original_matrix_bytes)
            self.assertEqual(
                harness.verify_matrix_artifact(matrix_path)["identity"],
                matrix["identity"],
            )

            access_item = next(
                item
                for item in matrix["artifacts"]
                if item["kind"] == "build-file-access"
            )
            access_report = json.loads(
                (out_dir / access_item["artifact"]).read_text(
                    encoding="utf-8"
                )
            )
            self.assertTrue(access_report["accessSetsEqual"])
            self.assertTrue(access_report["reportedInputsEqual"])
            self.assertEqual(
                [attempt["reportedInputCount"] for attempt in access_report["attempts"]],
                [1, 1],
            )
            replay_item = next(
                item
                for item in matrix["artifacts"]
                if item["kind"] == "build-input-replay"
            )
            replay_report = json.loads(
                (out_dir / replay_item["artifact"]).read_text(
                    encoding="utf-8"
                )
            )
            self.assertTrue(replay_report["equal"])
            self.assertTrue(replay_report["productsEqual"])
            self.assertTrue(replay_report["buildInputsEqual"])
            self.assertEqual(replay_report["sourceAttempt"], 2)
            self.assertEqual(
                [binding["category"] for binding in replay_report["bindings"]],
                ["build-input", "build-tool", "validation-input"],
            )
            self.assertEqual(replay_report["reportedInputCount"], 1)
            self.assertEqual(
                replay_report["reportedInputs"][0]["sha256"],
                material_sha256,
            )
            status_item = next(
                item
                for item in matrix["artifacts"]
                if item["kind"] == "build-input-replay-status"
            )
            core.parse_bwrap_status(
                (out_dir / status_item["artifact"]).read_bytes(),
                "retained fake sandbox status",
            )

            tampered_replay_report = json.loads(json.dumps(replay_report))
            tampered_replay_report["bindings"][0]["mode"] = 0o555
            tampered_replay_content = (
                json.dumps(
                    tampered_replay_report, indent=2, sort_keys=True
                )
                + "\n"
            ).encode("utf-8")
            tampered_replay_sha256 = harness.sha256_bytes(
                tampered_replay_content
            )
            (
                out_dir
                / "evidence"
                / "artifacts"
                / tampered_replay_sha256
            ).write_bytes(tampered_replay_content)
            tampered_replay_matrix = json.loads(original_matrix_bytes)
            tampered_replay_item = next(
                item
                for item in tampered_replay_matrix["artifacts"]
                if item["kind"] == "build-input-replay"
            )
            tampered_replay_item["sha256"] = tampered_replay_sha256
            tampered_replay_item["artifact"] = (
                f"evidence/artifacts/{tampered_replay_sha256}"
            )
            matrix_path.write_text(
                json.dumps(
                    tampered_replay_matrix, indent=2, sort_keys=True
                )
                + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "bindings disagree with source evidence",
            ):
                harness.verify_matrix_artifact(matrix_path)
            matrix_path.write_bytes(original_matrix_bytes)

            tampered_access_report = json.loads(
                json.dumps(access_report)
            )
            tampered_access_report["attempts"][0]["accesses"].pop()
            tampered_access_content = (
                json.dumps(
                    tampered_access_report, indent=2, sort_keys=True
                )
                + "\n"
            ).encode("utf-8")
            tampered_access_sha256 = harness.sha256_bytes(
                tampered_access_content
            )
            (
                out_dir
                / "evidence"
                / "artifacts"
                / tampered_access_sha256
            ).write_bytes(tampered_access_content)
            tampered_matrix = json.loads(original_matrix_bytes)
            tampered_access_item = next(
                item
                for item in tampered_matrix["artifacts"]
                if item["kind"] == "build-file-access"
            )
            tampered_access_item["sha256"] = tampered_access_sha256
            tampered_access_item["artifact"] = (
                f"evidence/artifacts/{tampered_access_sha256}"
            )
            matrix_path.write_text(
                json.dumps(tampered_matrix, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "disagrees with parsed trace",
            ):
                harness.verify_matrix_artifact(matrix_path)
            matrix_path.write_bytes(original_matrix_bytes)

            missing_access_matrix = json.loads(original_matrix_bytes)
            missing_access_matrix["artifacts"] = [
                item
                for item in missing_access_matrix["artifacts"]
                if item["kind"]
                not in {
                    "build-file-access",
                    "build-file-access-trace",
                }
            ]
            missing_access_matrix["summary"]["artifactCount"] -= 3
            matrix_path.write_text(
                json.dumps(
                    missing_access_matrix, indent=2, sort_keys=True
                )
                + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "recorder tools disagree with reports",
            ):
                harness.verify_matrix_artifact(matrix_path)
            matrix_path.write_bytes(original_matrix_bytes)

            tampered_matrix = json.loads(original_matrix_bytes)
            tampered_matrix["buildInputs"].pop()
            tampered_matrix["summary"]["buildInputCount"] -= 1
            matrix_path.write_text(
                json.dumps(tampered_matrix, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "require exactly one manifest|disagrees with matrix build inputs",
            ):
                harness.verify_matrix_artifact(matrix_path)
            matrix_path.write_bytes(original_matrix_bytes)

            plan_path.unlink()
            adapter_path.unlink()
            runner_path.unlink()
            material_path.unlink()
            recorder_path.unlink()
            isolator_path.unlink()
            product_path.unlink()
            (out_dir / "comparisons" / "native--v8.json").unlink()
            for item in matrix["artifacts"]:
                (out_dir / item["name"]).unlink(missing_ok=True)
            matrix_path.unlink()
            self.assertEqual(
                harness.verify_evidence_manifest(evidence_path)["identity"],
                evidence["identity"],
            )
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "validate_interpreters.py",
                        "--verify-evidence",
                        str(evidence_path),
                    ],
                ),
                contextlib.redirect_stdout(io.StringIO()) as evidence_stdout,
            ):
                self.assertEqual(harness.main(), 0)
            self.assertIn(
                evidence["identity"]["evidence"], evidence_stdout.getvalue()
            )
            self.assertIn("coverage results:", evidence_stdout.getvalue())
            matrix_path.write_bytes(original_matrix_bytes)
            self.assertEqual(
                harness.verify_matrix_artifact(matrix_path)["identity"],
                matrix["identity"],
            )
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["validate_interpreters.py", "--verify-matrix", str(matrix_path)],
                ),
                contextlib.redirect_stdout(io.StringIO()) as verify_stdout,
            ):
                self.assertEqual(harness.main(), 0)
            self.assertIn(matrix["identity"]["run"], verify_stdout.getvalue())
            self.assertIn("coverage backend native:", verify_stdout.getvalue())

            invalid_matrix = json.loads(original_matrix_bytes)
            invalid_matrix["coverage"]["backends"][0][
                "successfulCaseCount"
            ] = 0
            matrix_path.write_text(
                json.dumps(invalid_matrix, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "coverage disagrees with retained evidence",
            ):
                harness.verify_matrix_artifact(matrix_path)
            matrix_path.write_bytes(original_matrix_bytes)

            retained_matrix = out_dir / evidence["matrix"]["artifact"]
            retained_matrix_bytes = retained_matrix.read_bytes()
            retained_matrix.write_bytes(b"tampered retained matrix")
            with self.assertRaisesRegex(harness.ValidationError, "SHA-256 mismatch"):
                harness.verify_evidence_manifest(evidence_path)
            retained_matrix.write_bytes(retained_matrix_bytes)

            retained_input = out_dir / matrix["inputs"][1]["artifact"]
            retained_bytes = retained_input.read_bytes()
            retained_input.write_bytes(b"tampered")
            with self.assertRaisesRegex(harness.ValidationError, "SHA-256 mismatch"):
                harness.verify_matrix_artifact(matrix_path)
            retained_input.write_bytes(retained_bytes)

            retained_artifact = out_dir / matrix["artifacts"][0]["artifact"]
            retained_artifact_bytes = retained_artifact.read_bytes()
            retained_artifact.write_bytes(b"tampered artifact")
            with self.assertRaisesRegex(harness.ValidationError, "SHA-256 mismatch"):
                harness.verify_matrix_artifact(matrix_path)
            retained_artifact.write_bytes(retained_artifact_bytes)

            invalid_matrix = dict(matrix)
            invalid_matrix["summary"] = dict(matrix["summary"])
            invalid_matrix["summary"]["inputCount"] = False
            matrix_path.write_text(json.dumps(invalid_matrix), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "summary"
            ):
                harness.verify_matrix_artifact(matrix_path)

            invalid_matrix = dict(matrix)
            invalid_matrix["identity"] = dict(matrix["identity"])
            invalid_matrix["identity"]["run"] = "0" * 64
            matrix_path.write_text(json.dumps(invalid_matrix), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "run identity mismatch"
            ):
                harness.verify_matrix_artifact(matrix_path)

            invalid_matrix = dict(matrix)
            invalid_matrix["artifacts"] = [
                item
                for item in matrix["artifacts"]
                if not (
                    item["kind"] == "backend-result"
                    and item["name"] == "case/v8/result.json"
                )
            ]
            invalid_matrix["summary"] = dict(matrix["summary"])
            invalid_matrix["summary"]["artifactCount"] -= 1
            matrix_path.write_text(json.dumps(invalid_matrix), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "no retained backend result"
            ):
                harness.verify_matrix_artifact(matrix_path)

            native_result = next(
                item
                for item in matrix["artifacts"]
                if item["name"] == "case/native/result.json"
            )
            invalid_matrix = dict(matrix)
            invalid_matrix["artifacts"] = [
                (
                    {
                        **item,
                        "sha256": native_result["sha256"],
                        "artifact": native_result["artifact"],
                    }
                    if item["name"] == "case/v8/result.json"
                    else item
                )
                for item in matrix["artifacts"]
            ]
            matrix_path.write_text(json.dumps(invalid_matrix), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "expected backend v8, got native"
            ):
                harness.verify_matrix_artifact(matrix_path)

            invalid_matrix = dict(matrix)
            invalid_matrix["artifacts"] = [
                item
                for item in matrix["artifacts"]
                if not (
                    item["kind"] == "process-stderr"
                    and item["name"] == "v8/stderr.log"
                )
            ]
            invalid_matrix["summary"] = dict(matrix["summary"])
            invalid_matrix["summary"]["artifactCount"] -= 1
            matrix_path.write_text(json.dumps(invalid_matrix), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "process artifacts are not paired"
            ):
                harness.verify_matrix_artifact(matrix_path)

            valid_with_finding = dict(matrix)
            valid_with_finding["findings"] = [
                {"phase": "comparison", "message": "retained mismatch"}
            ]
            valid_with_finding["summary"] = dict(matrix["summary"])
            valid_with_finding["summary"]["findingCount"] = 1
            valid_with_finding["coverage"] = json.loads(
                json.dumps(matrix["coverage"])
            )
            valid_with_finding["coverage"]["findingCount"] = 1
            valid_with_finding["coverage"]["unassignedFindingCount"] = 1
            matrix_path.write_text(
                json.dumps(valid_with_finding), encoding="utf-8"
            )
            self.assertEqual(
                harness.verify_matrix_artifact(matrix_path)["findings"],
                valid_with_finding["findings"],
            )

            evidence_bytes = evidence_path.read_bytes()
            invalid_evidence = json.loads(evidence_bytes)
            invalid_evidence["coverage"]["backendResultCount"] = 0
            evidence_path.write_text(
                json.dumps(invalid_evidence), encoding="utf-8"
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "evidence coverage disagrees with retained matrix",
            ):
                harness.verify_evidence_manifest(evidence_path)
            evidence_path.write_bytes(evidence_bytes)

            invalid_evidence = json.loads(evidence_bytes)
            invalid_evidence["identity"]["evidence"] = "0" * 64
            evidence_path.write_text(json.dumps(invalid_evidence), encoding="utf-8")
            with self.assertRaisesRegex(
                harness.ValidationError, "filename mismatch"
            ):
                harness.verify_evidence_manifest(evidence_path)
            evidence_path.write_bytes(evidence_bytes)

            wrong_name = evidence_path.with_name("0" * 64 + ".json")
            wrong_name.write_bytes(evidence_bytes)
            with self.assertRaisesRegex(
                harness.ValidationError, "filename mismatch"
            ):
                harness.verify_evidence_manifest(wrong_name)

    def test_external_adapter_receives_corpus_and_selection_environment(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            stale_build = out_dir / "v8" / "build"
            stale_build.mkdir(parents=True)
            (stale_build / "stdout.jsonl").write_text(
                "stale build stdout", encoding="utf-8"
            )
            (stale_build / "stderr.log").write_text(
                "stale build stderr", encoding="utf-8"
            )
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            record = success("case", "v8")
            program = (
                "import json,os,pathlib;"
                "execution=json.loads(pathlib.Path("
                "os.environ['FIR_VALIDATION_EXECUTION_INPUT']).read_text());"
                "assert execution['selectedCases'] == ['case'];"
                "assert 'FIR_VALIDATION_CASES' not in os.environ;"
                "assert 'FIR_VALIDATION_PRODUCTS' not in os.environ;"
                "assert 'FIR_VALIDATION_PRODUCT_BUNDLE' not in os.environ;"
                "assert json.loads(os.environ['FIR_VALIDATION_TOOLS']) == [];"
                "assert os.path.isfile(os.environ['FIR_VALIDATION_CORPUS']);"
                "assert os.environ['FIR_VALIDATION_BACKEND'] == 'v8';"
                f"assert os.getcwd() == {json.dumps(str(harness.ROOT))};"
                f"print({json.dumps(json.dumps(record))})"
            )
            adapter = harness.ExternalCommandAdapter(
                "v8", [sys.executable, "-c", program], "selected"
            )
            context = harness.RunContext(
                harness.ROOT, out_dir, descriptors, ["case"]
            )
            adapter.build(harness.BuildContext(harness.ROOT, out_dir, True))
            backend_run = adapter.execute(context)
            self.assertEqual(backend_run.findings, [])
            self.assertEqual(backend_run.expected_cases, ["case"])
            self.assertEqual(backend_run.results, {"case": record})
            self.assertEqual(
                [artifact.name for artifact in backend_run.artifacts],
                [
                    "v8/execution-input.json",
                    "v8/stdout.jsonl",
                    "v8/stderr.log",
                ],
            )
            self.assertTrue((out_dir / "v8" / "stdout.jsonl").is_file())

    def test_external_execution_input_scales_beyond_execve_arg_max(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            contract = harness.ProductContract(
                "wasm", "wasm32", "fixture", "fixture-v1"
            )
            products = tuple(
                harness.ValidationProduct(
                    "fixture-wasm",
                    "wasm-module",
                    f"modules/case-{index:05d}/module.wasm",
                    harness.sha256_bytes(f"module {index}".encode("utf-8")),
                )
                for index in range(7000)
            )
            case_products = (("case", products),)
            bundle = harness.ProductBundle(
                "fixture-wasm",
                contract,
                core.product_bundle_sha256(
                    "fixture-wasm",
                    contract,
                    products,
                    case_products,
                ),
                products,
                case_products,
            )
            record = success("case", "v8")
            program = (
                "import json,os,pathlib;"
                "path=pathlib.Path("
                "os.environ['FIR_VALIDATION_EXECUTION_INPUT']);"
                "execution=json.loads(path.read_text());"
                "assert len(execution['products'])==7000;"
                "assert len(execution['productBundle']['products'])==7000;"
                "assert 'FIR_VALIDATION_PRODUCTS' not in os.environ;"
                "assert 'FIR_VALIDATION_PRODUCT_BUNDLE' not in os.environ;"
                f"print({json.dumps(json.dumps(record))})"
            )
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                run_command=[sys.executable, "-c", program],
                result_domain="selected",
                product_provider=harness.ProductProviderRequirement(
                    bundle.provider, contract
                ),
            )
            context = harness.RunContext(
                root,
                out_dir,
                descriptors,
                ["case"],
                product_bundles={bundle.provider: bundle},
            )
            adapter.build(harness.BuildContext(root, out_dir, True, context))
            with mock.patch.object(
                core, "verify_product_bundle_files"
            ):
                backend_run = adapter.execute(context)
            execution_artifact = next(
                artifact
                for artifact in backend_run.artifacts
                if artifact.kind == "execution-input"
            )
            self.assertGreater(
                len(execution_artifact.content),
                os.sysconf("SC_ARG_MAX"),
            )
            self.assertEqual(backend_run.results, {"case": record})
            self.assertEqual(
                (out_dir / "v8" / "execution-input.json").stat().st_mode
                & 0o777,
                0o444,
            )

    def test_external_execution_input_rejects_tampering_and_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            context = harness.RunContext(
                root, out_dir, descriptors, ["case"]
            )
            mutate = (
                "import os,pathlib;"
                "path=pathlib.Path("
                "os.environ['FIR_VALIDATION_EXECUTION_INPUT']);"
                "path.chmod(0o644);"
                "path.write_bytes(b'mutated')"
            )
            adapter = harness.ExternalCommandAdapter(
                "v8", [sys.executable, "-c", mutate], "selected"
            )
            adapter.build(harness.BuildContext(root, out_dir, True, context))
            with self.assertRaisesRegex(
                harness.ValidationError,
                "external execution input changed during execution",
            ):
                adapter.execute(context)

            replace = (
                "import os,pathlib;"
                "path=pathlib.Path("
                "os.environ['FIR_VALIDATION_EXECUTION_INPUT']);"
                "content=path.read_bytes();"
                "path.unlink();"
                "path.write_bytes(content)"
            )
            adapter.run_command = [sys.executable, "-c", replace]
            adapter.build(harness.BuildContext(root, out_dir, True, context))
            with self.assertRaisesRegex(
                harness.ValidationError,
                "external execution input was replaced during execution",
            ):
                adapter.execute(context)

            execution_input = out_dir / "v8" / "execution-input.json"
            execution_input.unlink()
            target = root / "outside.json"
            target.write_text("outside", encoding="utf-8")
            execution_input.symlink_to(target)
            with self.assertRaisesRegex(
                harness.ValidationError,
                "execution input path is a symlink",
            ):
                adapter.execute(context)

    def test_external_adapter_binds_and_verifies_exact_declared_tools(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            runner = root / "runner.py"
            runner.write_bytes(b"original runner")
            engine_command = Path(sys.executable).name
            engine_path_text = shutil.which(engine_command)
            self.assertIsNotNone(engine_path_text)
            assert engine_path_text is not None
            engine_path = Path(engine_path_text).resolve()
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                run_command=[engine_command, str(runner)],
                result_domain="selected",
                tool_declarations=(
                    harness.ToolDeclaration(
                        "runner", "runner.py", path=runner
                    ),
                    harness.ToolDeclaration(
                        "engine", "python", command=engine_command
                    ),
                ),
            )
            build_context = harness.BuildContext(root, out_dir, True)
            adapter.build(build_context)
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            context = harness.RunContext(root, out_dir, descriptors, ["case"])
            failed = mock.Mock(returncode=7, stdout="", stderr="engine failed")
            with mock.patch.object(core, "run", return_value=failed) as run_mock:
                backend_run = adapter.execute(context)
            self.assertEqual(
                run_mock.call_args.args[0],
                [str(engine_path), str(runner.resolve())],
            )
            environment = run_mock.call_args.args[3]
            received_tools = json.loads(environment["FIR_VALIDATION_TOOLS"])
            self.assertEqual(
                [(tool["kind"], tool["name"]) for tool in received_tools],
                [("engine", "python"), ("runner", "runner.py")],
            )
            self.assertEqual(
                [tool["path"] for tool in received_tools],
                [str(engine_path), str(runner.resolve())],
            )
            self.assertEqual(
                [(tool.kind, tool.name) for tool in backend_run.tools],
                [("engine", "python"), ("runner", "runner.py")],
            )
            self.assertEqual(backend_run.findings[0].phase, "execution")

            runner.write_bytes(b"changed before execution")
            with self.assertRaisesRegex(
                harness.ValidationError, "tools changed between build and execution"
            ):
                adapter.execute(context)

            runner.write_bytes(b"original runner")
            adapter.build(build_context)

            def mutate_runner(*args: object, **kwargs: object) -> mock.Mock:
                runner.write_bytes(b"changed during execution")
                return failed

            with mock.patch.object(core, "run", side_effect=mutate_runner):
                with self.assertRaisesRegex(
                    harness.ValidationError, "tools changed during execution"
                ):
                    adapter.execute(context)

            missing = harness.ExternalCommandAdapter(
                name="missing",
                run_command=["fir-validation-command-that-does-not-exist"],
                result_domain="selected",
                tool_declarations=(
                    harness.ToolDeclaration(
                        "engine",
                        "missing",
                        command="fir-validation-command-that-does-not-exist",
                    ),
                ),
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "cannot resolve validation tool command"
            ):
                missing.build(build_context)

            unbound = harness.ExternalCommandAdapter(
                name="unbound",
                run_command=[engine_command, str(root / "different.py")],
                result_domain="selected",
                tool_declarations=(
                    harness.ToolDeclaration(
                        "engine", "python", command=engine_command
                    ),
                    harness.ToolDeclaration(
                        "runner", "runner.py", path=runner
                    ),
                ),
            )
            with self.assertRaisesRegex(
                harness.ValidationError,
                "path tool runner:runner.py must match exactly one runCommand argument",
            ):
                unbound.build(build_context)

    def test_external_adapter_binds_build_tools_before_build(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            builder = root / "builder.py"
            builder.write_bytes(b"original builder")
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            run_context = harness.RunContext(
                root, out_dir, descriptors, ["case"]
            )
            engine_command = Path(sys.executable).name
            engine_path_text = shutil.which(engine_command)
            self.assertIsNotNone(engine_path_text)
            assert engine_path_text is not None
            engine_path = Path(engine_path_text).resolve()
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                build_command=[engine_command, str(builder)],
                run_command=[engine_command, "-c", "raise SystemExit(7)"],
                result_domain="selected",
                build_tool_declarations=(
                    harness.ToolDeclaration(
                        "build-driver", "builder.py", path=builder
                    ),
                    harness.ToolDeclaration(
                        "build-launcher",
                        "python-build",
                        command=engine_command,
                    ),
                ),
                tool_declarations=(
                    harness.ToolDeclaration(
                        "engine", "python", command=engine_command
                    ),
                ),
            )
            completed = mock.Mock(returncode=0, stdout="", stderr="")
            build_context = harness.BuildContext(
                root, out_dir, False, run_context
            )
            with mock.patch.object(
                core, "run", return_value=completed
            ) as run_mock:
                adapter.build(build_context)
            self.assertEqual(
                run_mock.call_args.args[0],
                [str(engine_path), str(builder.resolve())],
            )
            build_environment = run_mock.call_args.args[3]
            build_tools = json.loads(
                build_environment["FIR_VALIDATION_BUILD_TOOLS"]
            )
            self.assertEqual(
                [(tool["kind"], tool["name"]) for tool in build_tools],
                [
                    ("build-driver", "builder.py"),
                    ("build-launcher", "python-build"),
                ],
            )
            self.assertEqual(
                [tool["path"] for tool in build_tools],
                [str(builder.resolve()), str(engine_path)],
            )

            failed = mock.Mock(returncode=7, stdout="", stderr="failed")
            with mock.patch.object(core, "run", return_value=failed):
                backend_run = adapter.execute(run_context)
            self.assertEqual(
                [(tool.kind, tool.name) for tool in backend_run.tools],
                [
                    ("build-driver", "builder.py"),
                    ("build-launcher", "python-build"),
                    ("engine", "python"),
                ],
            )

            builder.write_bytes(b"changed before execution")
            with self.assertRaisesRegex(
                harness.ValidationError,
                "tools changed between build and execution",
            ):
                adapter.execute(run_context)

            builder.write_bytes(b"original builder")

            def mutate_builder(*args: object, **kwargs: object) -> mock.Mock:
                builder.write_bytes(b"changed during build")
                return completed

            with mock.patch.object(core, "run", side_effect=mutate_builder):
                with self.assertRaisesRegex(
                    harness.ValidationError, "tools changed during build"
                ):
                    adapter.build(build_context)

            adapter.build(
                harness.BuildContext(root, out_dir, True, run_context)
            )
            with mock.patch.object(core, "run", return_value=failed) as run_mock:
                backend_run = adapter.execute(run_context)
            self.assertEqual(
                [(tool.kind, tool.name) for tool in backend_run.tools],
                [("engine", "python")],
            )
            self.assertEqual(
                json.loads(
                    run_mock.call_args.args[3][
                        "FIR_VALIDATION_BUILD_TOOLS"
                    ]
                ),
                [],
            )

    def test_native_adapter_executes_the_captured_binary_directly(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            executable = root / "fir-native-oracle"
            executable.write_bytes(b"captured native executable")
            adapter = harness.NativeAdapter()
            with mock.patch.object(
                harness, "resolve_lake_command", return_value=executable
            ):
                adapter.build(harness.BuildContext(root, root / "out", True))

            record = success("case", "native")
            completed = mock.Mock(
                returncode=0,
                stdout=json.dumps(record) + "\n",
                stderr="",
            )
            context = harness.RunContext(
                root, root / "out", [descriptor("case")], ["case"]
            )
            with mock.patch.object(harness, "run", return_value=completed) as run_mock:
                backend_run = adapter.execute(context)
            command = run_mock.call_args.args[0]
            self.assertEqual(command, [str(executable), "--case", "case"])
            self.assertNotIn("lake", command)
            self.assertEqual(backend_run.results, {"case": record})
            self.assertEqual(
                [(tool.kind, tool.name) for tool in backend_run.tools],
                [("executable", ".lake/build/bin/fir-native-oracle")],
            )

            executable.write_bytes(b"mutated native executable")
            with self.assertRaisesRegex(
                harness.ValidationError, "executable changed during run"
            ):
                adapter.execute(context)

    def test_external_products_fail_closed_on_missing_escape_and_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory) / "out"
            backend_dir = out_dir / "v8"
            backend_dir.mkdir(parents=True)
            declaration = harness.ProductDeclaration(
                "wasm-module", "module.wasm"
            )
            adapter = harness.ExternalCommandAdapter(
                name="v8",
                build_command=[sys.executable, "-c", "pass"],
                run_command=[sys.executable, "-c", "pass"],
                result_domain="selected",
                product_declarations=(declaration,),
            )
            build_context = harness.BuildContext(harness.ROOT, out_dir, True)

            with self.assertRaisesRegex(
                harness.ValidationError, "product is not a regular file"
            ):
                adapter.build(build_context)

            outside = Path(directory) / "outside.wasm"
            outside.write_bytes(b"outside")
            (backend_dir / "module.wasm").symlink_to(outside)
            with self.assertRaisesRegex(
                harness.ValidationError, "product escapes its output directory"
            ):
                adapter.build(build_context)
            (backend_dir / "module.wasm").unlink()

            module = backend_dir / "module.wasm"
            module.write_bytes(b"before")
            mutating_program = (
                "import os,pathlib;"
                "pathlib.Path(os.environ['FIR_VALIDATION_OUT_DIR'],"
                "'module.wasm').write_bytes(b'after')"
            )
            adapter.run_command = [sys.executable, "-c", mutating_program]
            adapter.build(build_context)
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            context = harness.RunContext(
                harness.ROOT, out_dir, descriptors, ["case"]
            )
            with self.assertRaisesRegex(
                harness.ValidationError, "products changed during execution"
            ):
                adapter.execute(context)

            module.write_bytes(b"stale")
            with self.assertRaisesRegex(
                harness.ValidationError, "product is not a regular file"
            ):
                adapter.build(
                    harness.BuildContext(harness.ROOT, out_dir, False)
                )

    def test_coverage_separates_static_and_executed_forms(self) -> None:
        manifest = [
            descriptor("b-case", forms=["lit"], executed_forms=["lit"]),
            descriptor("a-case", forms=["return"]),
        ]
        results = {
            "a-case": with_form_diagnostics(
                success("a-case", "lcnf"), static="return, inc", executed="inc"
            ),
            "b-case": with_form_diagnostics(
                success("b-case", "lcnf"), static="lit", executed="lit"
            ),
        }
        report, failures = harness.coverage_report(
            manifest, results, ["b-case", "a-case"]
        )
        self.assertEqual(failures, [])
        self.assertEqual([case["caseId"] for case in report["cases"]], ["a-case", "b-case"])
        self.assertEqual(
            report["summary"]["static"],
            {
                "requiredForms": ["lit", "return"],
                "observedForms": ["inc", "lit", "return"],
                "missingObligationCount": 0,
            },
        )
        self.assertEqual(
            report["summary"]["executed"],
            {
                "casesWithRequirements": 1,
                "casesWithDiagnostics": 2,
                "requiredForms": ["lit"],
                "observedForms": ["inc", "lit"],
                "missingObligationCount": 0,
                "formCounts": {
                    "casesWithRequirements": 0,
                    "casesWithUpperBounds": 0,
                    "casesWithZeroRequirements": 0,
                    "zeroRequirementCount": 0,
                    "casesWithDiagnostics": 2,
                    "casesWithValidDiagnostics": 2,
                    "requiredMinimums": [],
                    "boundedMaximums": [],
                    "observed": [
                        {"form": "inc", "count": 1},
                        {"form": "lit", "count": 1},
                    ],
                    "unsatisfiedObligationCount": 0,
                },
                "formTrace": {
                    "casesWithRequirements": 0,
                    "casesWithDiagnostics": 2,
                    "casesWithValidDiagnostics": 2,
                    "casesWithConsistentDiagnostics": 2,
                    "mismatchedObligationCount": 0,
                    "observedEventCount": 2,
                },
                "staticConsistency": {
                    "casesConsistent": 2,
                    "unexpectedFormCount": 0,
                },
                "stepTrace": {
                    "casesWithDiagnostics": 2,
                    "casesWithValidDiagnostics": 2,
                    "casesWithCompleteCoverage": 2,
                    "casesWithConsistentFormProjection": 2,
                    "observedStepCount": 2,
                    "classifiedStepCount": 2,
                    "unclassifiedStepCount": 0,
                    "formStepCount": 2,
                    "administrativeStepCount": 0,
                    "administrativeKinds": [],
                    "casesWithAdministrativeRequirements": 0,
                    "requiredAdministrativeKinds": [],
                    "missingAdministrativeObligationCount": 0,
                    "unobservedAdministrativeKinds": sorted(
                        lcnf.ADMINISTRATIVE_STEP_KINDS
                    ),
                },
                "totalInterpreterSteps": 2,
                "minimumInterpreterSteps": 1,
                "maximumInterpreterSteps": 1,
            },
        )
        self.assertFalse(report["cases"][0]["executed"]["obligationsActive"])
        self.assertEqual(report["cases"][0]["executed"]["observedForms"], ["inc"])

    def test_static_coverage_obligations_are_enforced_from_observed_forms(self) -> None:
        manifest = [descriptor("case", forms=["inc", "return"])]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"), static="return", executed="return"
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing required static LCNF forms: inc"],
        )
        self.assertEqual(
            failures[0].to_json(),
            {
                "phase": "audit",
                "message": "missing required static LCNF forms: inc",
                "backend": "lcnf",
                "caseId": "case",
            },
        )
        self.assertEqual(
            report["cases"][0]["static"]["missingRequiredForms"], ["inc"]
        )

    def test_executed_telemetry_is_required_without_obligations(self) -> None:
        manifest = [descriptor("case", forms=["return"])]
        results = {
            "case": with_form_diagnostics(success("case", "lcnf"), static="return")
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: missing executed-lcnf-forms diagnostic",
                "case: missing executed-lcnf-form-counts diagnostic",
                "case: missing executed-lcnf-form-trace diagnostic",
                "case: missing executed-step-trace diagnostic",
            ],
        )
        executed = report["cases"][0]["executed"]
        self.assertFalse(executed["diagnosticPresent"])
        self.assertFalse(executed["obligationsActive"])
        self.assertEqual(executed["missingRequiredForms"], [])

    def test_interpreter_steps_must_be_present_and_positive(self) -> None:
        manifest = [descriptor("case")]
        missing = {
            "case": with_form_diagnostics(
                success("case", "lcnf"), static="return", executed="return", steps=None
            )
        }
        _, failures = harness.coverage_report(manifest, missing, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing interpreter-steps diagnostic"],
        )

        for invalid in ("0", "-1", "many"):
            with self.subTest(invalid=invalid):
                results = {
                    "case": with_form_diagnostics(
                        success("case", "lcnf"),
                        static="return",
                        executed="return",
                        steps=invalid,
                    )
                }
                _, failures = harness.coverage_report(manifest, results, ["case"])
                self.assertEqual(
                    finding_messages(failures),
                    ["case: interpreter-steps must be a positive integer"],
                )

    def test_declared_executed_coverage_obligations_are_enforced(self) -> None:
        manifest = [
            descriptor(
                "case", forms=["return"], executed_forms=["cases", "return"]
            )
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"), static="cases,return", executed="return"
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing required executed LCNF forms: cases"],
        )
        self.assertEqual(
            report["cases"][0]["executed"]["missingRequiredForms"], ["cases"]
        )

    def test_executed_form_count_obligations_are_enforced(self) -> None:
        manifest = [
            descriptor(
                "case",
                forms=["oset", "return"],
                executed_forms=["oset", "return"],
                executed_form_counts=[
                    {"form": "oset", "minimum": 2, "maximum": 2}
                ],
            )
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="oset,return",
                executed="oset,return",
                executed_counts=json.dumps(
                    [
                        {"form": "return", "count": 3},
                        {"form": "oset", "count": 1},
                    ]
                ),
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed LCNF form counts outside required bounds: "
                "oset=1<2"
            ],
        )
        counts = report["cases"][0]["executed"]["formCounts"]
        self.assertTrue(counts["diagnosticPresent"])
        self.assertTrue(counts["diagnosticValid"])
        self.assertTrue(counts["obligationsActive"])
        self.assertTrue(counts["upperBoundsActive"])
        self.assertFalse(counts["zeroCountsActive"])
        self.assertEqual(
            counts["required"],
            [{"form": "oset", "minimum": 2, "maximum": 2}],
        )
        self.assertEqual(
            counts["observed"],
            [
                {"form": "oset", "count": 1},
                {"form": "return", "count": 3},
            ],
        )
        self.assertEqual(
            counts["requiredObservations"],
            [{"form": "oset", "count": 1}],
        )
        self.assertEqual(
            counts["unsatisfied"],
            [{"form": "oset", "minimum": 2, "maximum": 2, "observed": 1}],
        )
        self.assertEqual(
            report["summary"]["executed"]["formCounts"],
            {
                "casesWithRequirements": 1,
                "casesWithUpperBounds": 1,
                "casesWithZeroRequirements": 0,
                "zeroRequirementCount": 0,
                "casesWithDiagnostics": 1,
                "casesWithValidDiagnostics": 1,
                "requiredMinimums": [{"form": "oset", "minimum": 2}],
                "boundedMaximums": [{"form": "oset", "maximum": 2}],
                "observed": [
                    {"form": "oset", "count": 1},
                    {"form": "return", "count": 3},
                ],
                "unsatisfiedObligationCount": 1,
            },
        )

        results["case"] = with_form_diagnostics(
            success("case", "lcnf"),
            static="oset,return",
            executed="oset,return",
            executed_counts=json.dumps(
                [
                    {"form": "return", "count": 3},
                    {"form": "oset", "count": 3},
                ]
            ),
        )
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed LCNF form counts outside required bounds: "
                "oset=3>2"
            ],
        )
        self.assertEqual(
            report["cases"][0]["executed"]["formCounts"]["unsatisfied"],
            [{"form": "oset", "minimum": 2, "maximum": 2, "observed": 3}],
        )

    def test_zero_form_count_obligation_enforces_path_exclusion(self) -> None:
        manifest = [
            descriptor(
                "case",
                forms=["oset", "return"],
                executed_forms=["return"],
                executed_form_counts=[
                    {"form": "oset", "minimum": 0, "maximum": 0}
                ],
            )
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="oset,return",
                executed="return",
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(failures, [])
        counts = report["cases"][0]["executed"]["formCounts"]
        self.assertTrue(counts["zeroCountsActive"])
        self.assertEqual(
            counts["requiredObservations"],
            [{"form": "oset", "count": 0}],
        )
        self.assertEqual(counts["unsatisfied"], [])
        summary = report["summary"]["executed"]["formCounts"]
        self.assertEqual(summary["casesWithZeroRequirements"], 1)
        self.assertEqual(summary["zeroRequirementCount"], 1)
        self.assertEqual(
            summary["boundedMaximums"],
            [{"form": "oset", "maximum": 0}],
        )

        results["case"] = with_form_diagnostics(
            success("case", "lcnf"),
            static="oset,return",
            executed="oset,return",
            executed_counts=(
                '[{"form":"oset","count":1},{"form":"return","count":1}]'
            ),
        )
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed LCNF form counts outside required bounds: "
                "oset=1>0"
            ],
        )
        self.assertEqual(
            report["cases"][0]["executed"]["formCounts"]["unsatisfied"],
            [{"form": "oset", "minimum": 0, "maximum": 0, "observed": 1}],
        )

    def test_executed_form_count_diagnostic_is_required_and_consistent(self) -> None:
        manifest = [descriptor("case")]

        missing = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_counts=None,
            )
        }
        _, failures = harness.coverage_report(manifest, missing, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing executed-lcnf-form-counts diagnostic"],
        )

        malformed = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_counts='[{"form":"return","count":0}]',
            )
        }
        _, failures = harness.coverage_report(manifest, malformed, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-lcnf-form-counts must be a unique JSON array "
                "of positive form counts"
            ],
        )

        inconsistent = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="oset,return",
                executed="oset,return",
                executed_counts='[{"form":"oset","count":2}]',
            )
        }
        _, failures = harness.coverage_report(manifest, inconsistent, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-lcnf-form-counts diagnostic disagrees with "
                "executed-lcnf-forms",
                "case: executed-lcnf-form-trace diagnostic disagrees with "
                "executed-lcnf-forms",
            ],
        )

    def test_executed_form_trace_is_required_ordered_and_consistent(self) -> None:
        manifest = [descriptor("case")]

        missing = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_form_trace=None,
            )
        }
        _, failures = harness.coverage_report(manifest, missing, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing executed-lcnf-form-trace diagnostic"],
        )

        malformed = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_form_trace='["return",1]',
            )
        }
        _, failures = harness.coverage_report(manifest, malformed, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-lcnf-form-trace must be a JSON array of "
                "nonempty form names"
            ],
        )

        inconsistent_counts = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="cases,return",
                executed="cases,return",
                executed_counts=(
                    '[{"form":"cases","count":2},'
                    '{"form":"return","count":1}]'
                ),
                executed_form_trace='["cases","return"]',
            )
        }
        _, failures = harness.coverage_report(
            manifest, inconsistent_counts, ["case"]
        )
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-lcnf-form-trace diagnostic disagrees with "
                "executed-lcnf-form-counts"
            ],
        )

        ordered = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="cases,lit,return",
                executed="cases,lit,return",
                executed_counts=(
                    '[{"form":"cases","count":1},'
                    '{"form":"lit","count":1},'
                    '{"form":"return","count":1}]'
                ),
                executed_form_trace='["cases","lit","return"]',
            )
        }
        report, failures = harness.coverage_report(manifest, ordered, ["case"])
        self.assertEqual(failures, [])
        trace = report["cases"][0]["executed"]["formTrace"]
        self.assertEqual(trace["observed"], ["cases", "lit", "return"])
        self.assertTrue(trace["namesConsistent"])
        self.assertTrue(trace["countsConsistent"])

        exact_manifest = [
            descriptor(
                "case",
                forms=["cases", "lit", "return"],
                executed_forms=["cases", "lit", "return"],
                required_executed_form_trace=["lit", "cases", "return"],
            )
        ]
        report, failures = harness.coverage_report(
            exact_manifest, ordered, ["case"]
        )
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed LCNF form trace differs from exact requirement "
                '(required=["lit","cases","return"];'
                ' observed=["cases","lit","return"])'
            ],
        )
        trace = report["cases"][0]["executed"]["formTrace"]
        self.assertTrue(trace["obligationsActive"])
        self.assertFalse(trace["matchesRequired"])
        self.assertEqual(
            report["summary"]["executed"]["formTrace"][
                "mismatchedObligationCount"
            ],
            1,
        )

    def test_executed_step_trace_covers_steps_and_administrative_kinds(self) -> None:
        manifest = [descriptor("case", forms=["return"])]
        administrative_kinds = sorted(lcnf.ADMINISTRATIVE_STEP_KINDS)
        step_trace = [
            "admin:invoke-name",
            "form:return",
            *administrative_kinds,
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_step_trace=json.dumps(step_trace),
                steps=str(len(step_trace)),
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(failures, [])
        coverage = report["cases"][0]["executed"]["stepTrace"]
        self.assertTrue(coverage["diagnosticValid"])
        self.assertTrue(coverage["completeCoverage"])
        self.assertTrue(coverage["formProjectionConsistent"])
        self.assertEqual(coverage["formSteps"], ["return"])
        expected_counts = {
            kind: 1 for kind in administrative_kinds
        }
        expected_counts["admin:invoke-name"] += 1
        self.assertEqual(
            coverage["administrativeCounts"],
            [
                {"kind": kind, "count": count}
                for kind, count in sorted(expected_counts.items())
            ],
        )
        summary = report["summary"]["executed"]["stepTrace"]
        self.assertEqual(summary["observedStepCount"], len(step_trace))
        self.assertEqual(summary["classifiedStepCount"], len(step_trace))
        self.assertEqual(summary["unclassifiedStepCount"], 0)
        self.assertEqual(summary["formStepCount"], 1)
        self.assertEqual(
            summary["administrativeStepCount"], len(step_trace) - 1
        )
        self.assertEqual(summary["unobservedAdministrativeKinds"], [])

    def test_lcnf_coverage_retains_custom_backend_identity(self) -> None:
        manifest = [
            descriptor(
                "case",
                forms=["return"],
                required_administrative_step_kinds=["admin:yield-apply"],
            )
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "direct-lcnf"),
                static="return",
                executed="return",
                executed_step_trace='["form:return"]',
                steps="1",
            )
        }
        report, failures = lcnf.coverage_report(
            manifest,
            results,
            ["case"],
            backend="direct-lcnf",
        )
        self.assertEqual(report["backend"], "direct-lcnf")
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0].backend, "direct-lcnf")
        self.assertEqual(
            failures[0].message,
            "missing required administrative step kinds: admin:yield-apply",
        )

    def test_administrative_step_kind_obligations_are_enforced(self) -> None:
        manifest = [
            descriptor(
                "case",
                forms=["return"],
                required_administrative_step_kinds=[
                    "admin:invoke-name",
                    "admin:yield-done",
                ],
            )
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_step_trace=(
                    '["admin:invoke-name","form:return","admin:yield-done"]'
                ),
                steps="3",
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(failures, [])
        coverage = report["cases"][0]["executed"]["stepTrace"]
        self.assertTrue(coverage["administrativeObligationsActive"])
        self.assertEqual(
            coverage["requiredAdministrativeKinds"],
            ["admin:invoke-name", "admin:yield-done"],
        )
        self.assertEqual(coverage["missingRequiredAdministrativeKinds"], [])
        summary = report["summary"]["executed"]["stepTrace"]
        self.assertEqual(summary["casesWithAdministrativeRequirements"], 1)
        self.assertEqual(
            summary["requiredAdministrativeKinds"],
            ["admin:invoke-name", "admin:yield-done"],
        )
        self.assertEqual(summary["missingAdministrativeObligationCount"], 0)

        missing = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_step_trace='["admin:invoke-name","form:return"]',
                steps="2",
            )
        }
        report, failures = harness.coverage_report(manifest, missing, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing required administrative step kinds: admin:yield-done"],
        )
        self.assertEqual(
            report["cases"][0]["executed"]["stepTrace"][
                "missingRequiredAdministrativeKinds"
            ],
            ["admin:yield-done"],
        )
        self.assertEqual(
            report["summary"]["executed"]["stepTrace"][
                "missingAdministrativeObligationCount"
            ],
            1,
        )

    def test_executed_step_trace_negative_coverage_paths(self) -> None:
        manifest = [descriptor("case", forms=["return"])]

        missing = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_step_trace=None,
            )
        }
        _, failures = harness.coverage_report(manifest, missing, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing executed-step-trace diagnostic"],
        )

        malformed = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_step_trace='["form:return",1]',
            )
        }
        _, failures = harness.coverage_report(manifest, malformed, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-step-trace must be a JSON array of "
                "nonempty step kinds"
            ],
        )

        unknown = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_step_trace=(
                    '["form:return","admin:not-classified"]'
                ),
                steps="2",
            )
        }
        _, failures = harness.coverage_report(manifest, unknown, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-step-trace contains unknown step kinds: "
                "admin:not-classified"
            ],
        )

        incomplete = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_step_trace='["form:return"]',
                steps="2",
            )
        }
        _, failures = harness.coverage_report(manifest, incomplete, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-step-trace does not cover every interpreter "
                "step (trace=1; steps=2)"
            ],
        )

        reordered_forms = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="cases,return",
                executed="cases,return",
                executed_counts=(
                    '[{"form":"cases","count":1},'
                    '{"form":"return","count":1}]'
                ),
                executed_form_trace='["cases","return"]',
                executed_step_trace='["form:return","form:cases"]',
                steps="2",
            )
        }
        _, failures = harness.coverage_report(
            manifest, reordered_forms, ["case"]
        )
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-step-trace form projection disagrees with "
                "executed-lcnf-form-trace"
            ],
        )

    def test_executed_forms_must_come_from_the_compiled_artifact(self) -> None:
        manifest = [descriptor("case", forms=["return"])]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="ghost,return",
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed LCNF forms absent from the compiled artifact: "
                "ghost"
            ],
        )
        self.assertEqual(
            report["cases"][0]["executed"]["staticConsistency"],
            {"consistent": False, "unexpectedForms": ["ghost"]},
        )

    def test_coverage_artifact_is_deterministic(self) -> None:
        manifest = [descriptor("case")]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"), static="return,return", executed="return"
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(failures, [])
        self.assertEqual(
            report["cases"][0]["static"]["observedForms"], ["return"]
        )
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            harness.write_coverage_artifact(out_dir, report)
            first = (out_dir / "coverage.json").read_bytes()
            harness.write_coverage_artifact(out_dir, report)
            self.assertEqual(first, (out_dir / "coverage.json").read_bytes())
            self.assertEqual(json.loads(first), report)

    def test_coverage_separates_static_and_executed_externals(self) -> None:
        manifest = [
            descriptor(
                "b-case",
                externals=["Nat.add"],
                executed_externals=["Nat.add"],
            ),
            descriptor("a-case"),
        ]
        results = {
            "a-case": with_form_diagnostics(
                success("a-case", "lcnf"),
                static="return",
                executed="return",
                static_externals="ByteArray.size",
            ),
            "b-case": with_form_diagnostics(
                success("b-case", "lcnf"),
                static="return,extern",
                executed="return,extern",
                static_externals="Nat.add,ByteArray.size,Nat.add",
                executed_externals="Nat.add",
            ),
        }
        report, failures = harness.coverage_report(
            manifest, results, ["b-case", "a-case"]
        )
        self.assertEqual(failures, [])
        self.assertEqual([case["caseId"] for case in report["cases"]], ["a-case", "b-case"])
        self.assertEqual(
            report["summary"]["externals"],
            {
                "static": {
                    "casesWithRequirements": 1,
                    "casesWithDiagnostics": 2,
                    "casesWithMissingDiagnostics": 2,
                    "requiredNames": ["Nat.add"],
                    "observedNames": ["ByteArray.size", "Nat.add"],
                    "missingObligationCount": 0,
                },
                "executed": {
                    "casesWithRequirements": 1,
                    "casesWithDiagnostics": 2,
                    "casesWithMissingDiagnostics": 2,
                    "requiredNames": ["Nat.add"],
                    "observedNames": ["Nat.add"],
                    "missingObligationCount": 0,
                    "counts": {
                        "casesWithRequirements": 0,
                        "casesWithUpperBounds": 0,
                        "casesWithZeroRequirements": 0,
                        "zeroRequirementCount": 0,
                        "casesWithDiagnostics": 2,
                        "casesWithValidDiagnostics": 2,
                        "requiredMinimums": [],
                        "boundedMaximums": [],
                        "observed": [{"external": "Nat.add", "count": 1}],
                        "unsatisfiedObligationCount": 0,
                    },
                    "trace": {
                        "casesWithRequirements": 0,
                        "casesWithDiagnostics": 2,
                        "casesWithValidDiagnostics": 2,
                        "casesWithConsistentDiagnostics": 2,
                        "mismatchedObligationCount": 0,
                        "observedEventCount": 1,
                    },
                },
            },
        )
        external = report["cases"][1]["externals"]
        self.assertEqual(
            external["static"]["observedNames"], ["ByteArray.size", "Nat.add"]
        )
        self.assertTrue(external["executed"]["obligationsActive"])

    def test_external_obligations_and_backend_missing_diagnostics_are_enforced(self) -> None:
        manifest = [
            descriptor(
                "case",
                externals=["ByteArray.size", "Nat.add"],
                executed_externals=["Nat.add"],
            )
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return,extern",
                executed="return",
                static_externals="ByteArray.size",
                missing_static_externals="Nat.add",
                executed_externals="",
                missing_executed_externals="Nat.add",
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: missing required static externals: Nat.add",
                "case: missing required executed externals: Nat.add",
            ],
        )
        self.assertEqual(
            report["cases"][0]["externals"]["static"]["reportedMissingNames"],
            ["Nat.add"],
        )

        results["case"] = with_form_diagnostics(
            success("case", "lcnf"),
            static="return,extern",
            executed="return,extern",
            static_externals="ByteArray.size,Nat.add",
            missing_static_externals="Ghost.external",
            executed_externals="Nat.add",
        )
        _, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: missing-externals diagnostic disagrees with obligations "
                "(reported=Ghost.external; computed=)"
            ],
        )

    def test_executed_external_count_obligations_are_enforced(self) -> None:
        manifest = [
            descriptor(
                "case",
                externals=["Nat.add"],
                executed_externals=["Nat.add"],
                executed_external_counts=[
                    {"external": "Nat.add", "minimum": 2, "maximum": 2}
                ],
            )
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="extern,return",
                executed="extern,return",
                static_externals="Nat.add",
                executed_externals="Nat.add",
                executed_external_counts=json.dumps(
                    [{"external": "Nat.add", "count": 1}]
                ),
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed external counts outside required bounds: "
                "Nat.add=1<2"
            ],
        )
        counts = report["cases"][0]["externals"]["executed"]["counts"]
        self.assertEqual(
            counts,
            {
                "diagnosticPresent": True,
                "diagnosticValid": True,
                "obligationsActive": True,
                "upperBoundsActive": True,
                "zeroCountsActive": False,
                "required": [
                    {"external": "Nat.add", "minimum": 2, "maximum": 2}
                ],
                "requiredObservations": [
                    {"external": "Nat.add", "count": 1}
                ],
                "observed": [{"external": "Nat.add", "count": 1}],
                "unsatisfied": [
                    {
                        "external": "Nat.add",
                        "minimum": 2,
                        "maximum": 2,
                        "observed": 1,
                    }
                ],
            },
        )
        self.assertEqual(
            report["summary"]["externals"]["executed"]["counts"],
            {
                "casesWithRequirements": 1,
                "casesWithUpperBounds": 1,
                "casesWithZeroRequirements": 0,
                "zeroRequirementCount": 0,
                "casesWithDiagnostics": 1,
                "casesWithValidDiagnostics": 1,
                "requiredMinimums": [{"external": "Nat.add", "minimum": 2}],
                "boundedMaximums": [{"external": "Nat.add", "maximum": 2}],
                "observed": [{"external": "Nat.add", "count": 1}],
                "unsatisfiedObligationCount": 1,
            },
        )

        results["case"] = with_form_diagnostics(
            success("case", "lcnf"),
            static="extern,return",
            executed="extern,return",
            static_externals="Nat.add",
            executed_externals="Nat.add",
            executed_external_counts=json.dumps(
                [{"external": "Nat.add", "count": 3}]
            ),
        )
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed external counts outside required bounds: "
                "Nat.add=3>2"
            ],
        )
        self.assertEqual(
            report["cases"][0]["externals"]["executed"]["counts"]["unsatisfied"],
            [
                {
                    "external": "Nat.add",
                    "minimum": 2,
                    "maximum": 2,
                    "observed": 3,
                }
            ],
        )

    def test_zero_external_count_obligation_enforces_path_exclusion(self) -> None:
        manifest = [
            descriptor(
                "case",
                externals=["Nat.add"],
                executed_external_counts=[
                    {"external": "Nat.add", "minimum": 0, "maximum": 0}
                ],
            )
        ]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                static_externals="Nat.add",
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(failures, [])
        counts = report["cases"][0]["externals"]["executed"]["counts"]
        self.assertTrue(counts["zeroCountsActive"])
        self.assertEqual(
            counts["requiredObservations"],
            [{"external": "Nat.add", "count": 0}],
        )
        self.assertEqual(counts["unsatisfied"], [])
        summary = report["summary"]["externals"]["executed"]["counts"]
        self.assertEqual(summary["casesWithZeroRequirements"], 1)
        self.assertEqual(summary["zeroRequirementCount"], 1)
        self.assertEqual(
            summary["boundedMaximums"],
            [{"external": "Nat.add", "maximum": 0}],
        )

        results["case"] = with_form_diagnostics(
            success("case", "lcnf"),
            static="return",
            executed="return",
            static_externals="Nat.add",
            executed_externals="Nat.add",
            executed_external_counts=(
                '[{"external":"Nat.add","count":1}]'
            ),
        )
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed external counts outside required bounds: "
                "Nat.add=1>0"
            ],
        )
        self.assertEqual(
            report["cases"][0]["externals"]["executed"]["counts"]["unsatisfied"],
            [
                {
                    "external": "Nat.add",
                    "minimum": 0,
                    "maximum": 0,
                    "observed": 1,
                }
            ],
        )

    def test_executed_external_count_diagnostic_is_required_and_consistent(self) -> None:
        manifest = [descriptor("case")]

        missing = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_external_counts=None,
            )
        }
        _, failures = harness.coverage_report(manifest, missing, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing executed-external-counts diagnostic"],
        )

        malformed = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="extern,return",
                executed="extern,return",
                executed_externals="Nat.add",
                executed_external_counts=(
                    '[{"external":"Nat.add","count":0}]'
                ),
            )
        }
        _, failures = harness.coverage_report(manifest, malformed, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-external-counts must be a unique JSON array "
                "of positive external counts"
            ],
        )

        inconsistent = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="extern,return",
                executed="extern,return",
                executed_externals="ByteArray.size,Nat.add",
                executed_external_counts=(
                    '[{"external":"Nat.add","count":2}]'
                ),
            )
        }
        _, failures = harness.coverage_report(manifest, inconsistent, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-external-counts diagnostic disagrees with "
                "executed-externals",
                "case: executed-external-trace diagnostic disagrees with "
                "executed-externals",
            ],
        )

    def test_executed_external_trace_is_required_ordered_and_consistent(self) -> None:
        manifest = [descriptor("case")]

        missing = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                executed_external_trace=None,
            )
        }
        _, failures = harness.coverage_report(manifest, missing, ["case"])
        self.assertEqual(
            finding_messages(failures),
            ["case: missing executed-external-trace diagnostic"],
        )

        malformed = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="extern,return",
                executed="extern,return",
                executed_externals="Nat.add",
                executed_external_trace='["Nat.add",1]',
            )
        }
        _, failures = harness.coverage_report(manifest, malformed, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-external-trace must be a JSON array of "
                "nonempty external names"
            ],
        )

        inconsistent_counts = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="extern,return",
                executed="extern,return",
                executed_externals="Nat.add",
                executed_external_counts=(
                    '[{"external":"Nat.add","count":2}]'
                ),
                executed_external_trace='["Nat.add"]',
            )
        }
        _, failures = harness.coverage_report(
            manifest, inconsistent_counts, ["case"]
        )
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed-external-trace diagnostic disagrees with "
                "executed-external-counts"
            ],
        )

        ordered = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="extern,return",
                executed="extern,return",
                static_externals="Nat.add,ByteArray.size",
                executed_externals="Nat.add,ByteArray.size",
                executed_external_counts=(
                    '[{"external":"Nat.add","count":1},'
                    '{"external":"ByteArray.size","count":1}]'
                ),
                executed_external_trace='["ByteArray.size","Nat.add"]',
            )
        }
        report, failures = harness.coverage_report(manifest, ordered, ["case"])
        self.assertEqual(failures, [])
        trace = report["cases"][0]["externals"]["executed"]["trace"]
        self.assertEqual(trace["observed"], ["ByteArray.size", "Nat.add"])
        self.assertTrue(trace["namesConsistent"])
        self.assertTrue(trace["countsConsistent"])

        exact_manifest = [
            descriptor(
                "case",
                externals=["ByteArray.size", "Nat.add"],
                executed_externals=["ByteArray.size", "Nat.add"],
                required_executed_external_trace=[
                    "Nat.add",
                    "ByteArray.size",
                ],
            )
        ]
        report, failures = harness.coverage_report(
            exact_manifest, ordered, ["case"]
        )
        self.assertEqual(
            finding_messages(failures),
            [
                "case: executed external trace differs from exact requirement "
                '(required=["Nat.add","ByteArray.size"];'
                ' observed=["ByteArray.size","Nat.add"])'
            ],
        )
        trace = report["cases"][0]["externals"]["executed"]["trace"]
        self.assertTrue(trace["obligationsActive"])
        self.assertFalse(trace["matchesRequired"])
        self.assertEqual(
            report["summary"]["externals"]["executed"]["trace"][
                "mismatchedObligationCount"
            ],
            1,
        )

        exact_empty_manifest = [
            descriptor(
                "case",
                externals=["Nat.add"],
                executed_external_counts=[
                    {"external": "Nat.add", "minimum": 0, "maximum": 0}
                ],
                required_executed_external_trace=[],
            )
        ]
        empty = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                static_externals="Nat.add",
            )
        }
        report, failures = harness.coverage_report(
            exact_empty_manifest, empty, ["case"]
        )
        self.assertEqual(failures, [])
        trace = report["cases"][0]["externals"]["executed"]["trace"]
        self.assertTrue(trace["obligationsActive"])
        self.assertEqual(trace["required"], [])
        self.assertTrue(trace["matchesRequired"])

    def test_external_telemetry_is_required_without_obligations(self) -> None:
        manifest = [descriptor("case")]
        results = {
            "case": with_form_diagnostics(
                success("case", "lcnf"),
                static="return",
                executed="return",
                static_externals=None,
                missing_static_externals=None,
                executed_externals=None,
                missing_executed_externals=None,
            )
        }
        report, failures = harness.coverage_report(manifest, results, ["case"])
        self.assertEqual(
            finding_messages(failures),
            [
                "case: missing externals diagnostic",
                "case: missing missing-externals diagnostic",
                "case: missing executed-externals diagnostic",
                "case: missing executed-external-counts diagnostic",
                "case: missing executed-external-trace diagnostic",
                "case: missing missing-executed-externals diagnostic",
            ],
        )
        self.assertFalse(
            report["cases"][0]["externals"]["executed"]["obligationsActive"]
        )

    def test_malformed_and_duplicate_diagnostics_are_rejected(self) -> None:
        malformed = success("case", "lcnf")
        malformed["diagnostics"] = "lcnf-forms=return"
        with self.assertRaisesRegex(harness.ValidationError, "malformed diagnostics"):
            harness.diagnostics(malformed)

        duplicate = success("case", "lcnf")
        duplicate["diagnostics"] = [
            {"key": "lcnf-forms", "value": "return"},
            {"key": "lcnf-forms", "value": "inc"},
        ]
        with self.assertRaisesRegex(harness.ValidationError, "duplicate diagnostic"):
            harness.diagnostics(duplicate)


class AttestationEnvelopeTests(unittest.TestCase):
    spec = attestation.EnvelopeSpec(
        kind="test-validation-evidence",
        contract_kind="test-validation-contract",
        contract_fields=("caseId", "claim"),
    )

    @staticmethod
    def validate_record(value: object) -> dict:
        if (
            not isinstance(value, dict)
            or set(value)
            != {"version", "identity", "caseId", "claim", "observation"}
            or value["version"] != 3
            or not isinstance(value["claim"], str)
            or not isinstance(value["observation"], int)
            or isinstance(value["observation"], bool)
        ):
            raise core.ValidationError("test attestation record is malformed")
        return value

    @staticmethod
    def record(case_id: str, claim: str, observation: int) -> dict:
        return attestation.with_record_identity(
            {
                "version": 3,
                "caseId": case_id,
                "claim": claim,
                "observation": observation,
            }
        )

    def test_generic_envelope_is_ordered_retained_and_relocatable(self) -> None:
        first = self.record("a-case", "returns the input", 41)
        second = self.record("b-case", "increments the input", 42)
        envelope = attestation.build_envelope(
            self.spec,
            [second, first],
            self.validate_record,
        )
        self.assertEqual(
            [record["caseId"] for record in envelope["records"]],
            ["a-case", "b-case"],
        )
        self.assertEqual(
            attestation.verify_envelope_value(
                envelope, self.spec, self.validate_record
            ),
            envelope,
        )
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            retained = attestation.write_retained_envelope(
                out_dir,
                "attestations.json",
                envelope,
                self.spec,
                self.validate_record,
            )
            expected = (
                "evidence/runs/"
                f"{envelope['identity']['contract']}/"
                f"{envelope['identity']['evidence']}.json"
            )
            self.assertEqual(retained, expected)
            self.assertEqual(
                attestation.read_envelope(
                    out_dir / retained,
                    self.spec,
                    self.validate_record,
                ),
                envelope,
            )
            moved = out_dir / "moved.json"
            shutil.copyfile(out_dir / retained, moved)
            self.assertEqual(
                attestation.read_envelope(
                    moved, self.spec, self.validate_record
                ),
                envelope,
            )

    def test_generic_envelope_separates_contract_and_evidence_drift(self) -> None:
        original_record = self.record("case", "returns the input", 41)
        original = attestation.build_envelope(
            self.spec, [original_record], self.validate_record
        )
        changed_observation = self.record("case", "returns the input", 42)
        evidence_drift = attestation.build_envelope(
            self.spec, [changed_observation], self.validate_record
        )
        self.assertEqual(
            original["identity"]["contract"],
            evidence_drift["identity"]["contract"],
        )
        self.assertNotEqual(
            original["identity"]["evidence"],
            evidence_drift["identity"]["evidence"],
        )
        changed_claim = self.record("case", "increments the input", 42)
        contract_drift = attestation.build_envelope(
            self.spec, [changed_claim], self.validate_record
        )
        self.assertNotEqual(
            original["identity"]["contract"],
            contract_drift["identity"]["contract"],
        )

        tampered = json.loads(json.dumps(original))
        tampered["records"][0]["observation"] = 99
        with self.assertRaisesRegex(
            core.ValidationError, "record identity does not match"
        ):
            attestation.verify_envelope_value(
                tampered, self.spec, self.validate_record
            )

        invalid_spec = attestation.EnvelopeSpec(
            kind="test",
            contract_kind="test-contract",
            contract_fields=("claim", "claim"),
        )
        with self.assertRaisesRegex(
            core.ValidationError, "unique and include the record ID"
        ):
            attestation.build_envelope(
                invalid_spec, [original_record], self.validate_record
            )

        mutating_record = json.loads(json.dumps(original_record))

        def mutating_validator(value: object) -> dict:
            assert isinstance(value, dict)
            value["observation"] = 99
            return value

        with self.assertRaisesRegex(
            core.ValidationError, "validator must preserve its input"
        ):
            attestation.build_envelope(
                self.spec, [mutating_record], mutating_validator
            )


class BackendComparisonAttestationTests(unittest.TestCase):
    selected_cases = ["case-a", "case-b"]
    source_evidence_sha256 = "4" * 64
    source_matrix_sha256 = "5" * 64

    def matrix(self, run_sha256: str = "2" * 64) -> dict:
        return {
            "version": 3,
            "identity": {
                "algorithm": "sha256",
                "selection": "1" * 64,
                "run": run_sha256,
            },
            "selectedCases": self.selected_cases,
            "backends": ["native", "v8"],
            "artifacts": [],
            "pairs": [],
        }

    def comparison_content(
        self,
        reference: str = "native",
        candidate: str = "v8",
        equal: tuple[bool, bool] = (True, True),
    ) -> bytes:
        value = {
            "version": 3,
            "reference": reference,
            "candidate": candidate,
            "comparisons": [
                {
                    "caseId": case_id,
                    "reference": reference,
                    "candidate": candidate,
                    "equal": case_equal,
                    "case": {"version": 3, "id": case_id},
                }
                for case_id, case_equal in zip(
                    self.selected_cases, equal, strict=True
                )
            ],
            "findings": [],
            "summary": {
                "selectedCases": 2,
                "comparedCases": 2,
                "equalCases": sum(int(item) for item in equal),
                "findingCount": 0,
            },
        }
        return (
            json.dumps(value, indent=2, sort_keys=True) + "\n"
        ).encode("utf-8")

    def result_artifacts(
        self,
        equal: tuple[bool, bool] = (True, True),
        candidate: str = "v8",
    ) -> dict[tuple[str, str], tuple[str, dict]]:
        result: dict[tuple[str, str], tuple[str, dict]] = {}
        for case_id, case_equal in zip(
            self.selected_cases, equal, strict=True
        ):
            reference_record = success(case_id, "native", 42)
            candidate_record = success(
                case_id, candidate, 42 if case_equal else 43
            )
            for backend, record in (
                ("native", reference_record),
                (candidate, candidate_record),
            ):
                content = (
                    json.dumps(record, indent=2, sort_keys=True) + "\n"
                ).encode("utf-8")
                result[(case_id, backend)] = (
                    core.sha256_bytes(content),
                    record,
                )
        return result

    def pair(
        self,
        content: bytes,
        reference: str = "native",
        candidate: str = "v8",
        equal_cases: int = 2,
    ) -> dict:
        digest = core.sha256_bytes(content)
        return {
            "reference": reference,
            "candidate": candidate,
            "artifact": f"evidence/comparisons/{digest}",
            "sha256": digest,
            "comparedCases": 2,
            "equalCases": equal_cases,
            "findingCount": 0,
        }

    def record(
        self,
        equal: tuple[bool, bool] = (True, True),
        run_sha256: str = "2" * 64,
        candidate: str = "v8",
        source_evidence_sha256: str | None = None,
        source_matrix_sha256: str | None = None,
    ) -> dict:
        content = self.comparison_content(
            candidate=candidate,
            equal=equal,
        )
        return comparison_attestations.record_from_verified_pair(
            self.matrix(run_sha256),
            self.pair(
                content,
                candidate=candidate,
                equal_cases=sum(int(item) for item in equal),
            ),
            content,
            self.result_artifacts(equal, candidate),
            source_evidence_sha256 or self.source_evidence_sha256,
            source_matrix_sha256 or self.source_matrix_sha256,
        )

    @staticmethod
    def policy(
        candidates: list[str] | None = None,
        minimum_cases: int = 2,
    ) -> dict:
        return {
            "version": 3,
            "kind": "fir-backend-comparison-oracle-policy",
            "oracle": "native",
            "requiredCandidates": candidates or ["lcnf", "v8"],
            "minimumCases": minimum_cases,
        }

    def test_evidence_adapter_retains_exact_edge_evidence_offline(self) -> None:
        content = self.comparison_content()
        matrix = self.matrix()
        pair = self.pair(content)
        matrix["pairs"] = [pair]
        result_artifacts = self.result_artifacts()
        result_contents: dict[str, bytes] = {}
        for (case_id, backend), (digest, record) in result_artifacts.items():
            artifact = f"evidence/artifacts/{digest}"
            matrix["artifacts"].append(
                {
                    "kind": "backend-result",
                    "name": f"{case_id}/{backend}/result.json",
                    "sha256": digest,
                    "artifact": artifact,
                }
            )
            result_contents[artifact] = (
                json.dumps(record, indent=2, sort_keys=True) + "\n"
            ).encode("utf-8")
        result_contents[pair["artifact"]] = content

        def evidence(
            _root: Path,
            artifact: str,
            _digest: str,
            _context: str,
        ) -> bytes:
            return result_contents[artifact]

        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            source_root = out_dir / "source"
            evidence_path = (
                source_root
                / "evidence"
                / "runs"
                / matrix["identity"]["run"]
                / f"{self.source_evidence_sha256}.json"
            )
            source = core.VerifiedEvidence(
                evidence_path,
                source_root,
                {
                    "identity": {
                        "evidence": self.source_evidence_sha256,
                    },
                    "matrix": {
                        "sha256": self.source_matrix_sha256,
                    },
                },
                matrix,
            )
            with (
                mock.patch.object(
                    comparison_attestations.core,
                    "verify_evidence_snapshot",
                    return_value=source,
                ) as verify_evidence,
                mock.patch.object(
                    comparison_attestations.core,
                    "verify_evidence_file",
                    side_effect=evidence,
                ) as verify_comparison,
            ):
                manifest = comparison_attestations.attest_evidence(
                    evidence_path, out_dir
                )
            verify_evidence.assert_called_once_with(evidence_path)
            verify_comparison.assert_any_call(
                source_root,
                pair["artifact"],
                pair["sha256"],
                "backend comparison attestation native->v8",
            )
            self.assertEqual(verify_comparison.call_count, 5)
            record = manifest["records"][0]
            self.assertEqual(
                record["sourceEvidenceSha256"],
                self.source_evidence_sha256,
            )
            self.assertEqual(
                record["sourceMatrixSha256"],
                self.source_matrix_sha256,
            )
            self.assertEqual(record["comparisonArtifact"], content.decode())
            self.assertEqual(record["comparisonArtifactBytes"], len(content))
            self.assertTrue(record["matches"])
            self.assertEqual(
                [witness["caseId"] for witness in record["witnesses"]],
                self.selected_cases,
            )
            self.assertTrue(
                all(witness["equal"] for witness in record["witnesses"])
            )
            retained = (
                out_dir
                / "evidence"
                / "runs"
                / manifest["identity"]["contract"]
                / f"{manifest['identity']['evidence']}.json"
            )
            self.assertEqual(
                comparison_attestations.verify_attestation_manifest(retained),
                manifest,
            )
            moved = out_dir / "moved.json"
            shutil.copyfile(retained, moved)
            policy_path = out_dir / "policy.json"
            policy_path.write_text(
                json.dumps(self.policy(["v8"])) + "\n",
                encoding="utf-8",
            )
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(
                    comparison_attestations.main(
                        [
                            "--verify-attestations",
                            str(moved),
                            "--policy",
                            str(policy_path),
                        ]
                    ),
                    0,
                )
            self.assertIn("matching edges 1/1", stdout.getvalue())
            self.assertIn(
                "accepted native comparison oracle for v8",
                stdout.getvalue(),
            )

    def test_receipt_adapter_uses_only_its_verified_snapshot(self) -> None:
        receipt_path = Path("evidence-receipt.json")
        source = core.VerifiedEvidence(
            Path("evidence/runs/run/evidence.json"),
            Path("."),
            {},
            {},
        )
        expected = [self.record()]
        with (
            mock.patch.object(
                comparison_attestations.core,
                "verify_evidence_receipt",
                return_value=source,
            ) as verify_receipt,
            mock.patch.object(
                comparison_attestations,
                "records_from_verified_evidence",
                return_value=expected,
            ) as records_from_source,
        ):
            records = comparison_attestations.records_from_evidence_receipt(
                receipt_path
            )
        self.assertEqual(records, expected)
        verify_receipt.assert_called_once_with(receipt_path)
        records_from_source.assert_called_once_with(source)

    def test_comparison_contract_is_separate_from_observed_evidence(self) -> None:
        original = comparison_attestations.build_attestation_manifest(
            [self.record()]
        )
        evidence_drift = comparison_attestations.build_attestation_manifest(
            [self.record(equal=(True, False))]
        )
        self.assertEqual(
            original["identity"]["contract"],
            evidence_drift["identity"]["contract"],
        )
        self.assertNotEqual(
            original["identity"]["evidence"],
            evidence_drift["identity"]["evidence"],
        )
        self.assertFalse(evidence_drift["records"][0]["matches"])

        source_drift = comparison_attestations.build_attestation_manifest(
            [self.record(source_evidence_sha256="6" * 64)]
        )
        self.assertEqual(
            original["identity"]["contract"],
            source_drift["identity"]["contract"],
        )
        self.assertNotEqual(
            original["identity"]["evidence"],
            source_drift["identity"]["evidence"],
        )

        contract_drift = comparison_attestations.build_attestation_manifest(
            [self.record(run_sha256="3" * 64)]
        )
        self.assertNotEqual(
            original["identity"]["contract"],
            contract_drift["identity"]["contract"],
        )

    def test_comparison_attestation_rejects_tampered_derivatives(self) -> None:
        record = self.record()
        malformed = dict(record)
        malformed.pop("identity")
        malformed["equalCases"] = 1
        malformed = attestation.with_record_identity(malformed)
        with self.assertRaisesRegex(
            core.ValidationError, "comparison derivatives disagree"
        ):
            comparison_attestations.verify_attestation_record(malformed)

        malformed = dict(record)
        malformed.pop("identity")
        malformed["comparisonArtifact"] += " "
        malformed = attestation.with_record_identity(malformed)
        with self.assertRaisesRegex(
            core.ValidationError, "artifact derivatives disagree"
        ):
            comparison_attestations.verify_attestation_record(malformed)

        malformed = json.loads(json.dumps(record))
        malformed.pop("identity")
        malformed["witnesses"][0]["candidateObservation"] = {
            "termination": {"trapped": {"message": "tampered"}}
        }
        malformed = attestation.with_record_identity(malformed)
        with self.assertRaisesRegex(
            core.ValidationError,
            "witnesses disagree with retained comparison evidence",
        ):
            comparison_attestations.verify_attestation_record(malformed)

        malformed = dict(record)
        malformed.pop("identity")
        malformed["sourceEvidenceSha256"] = "not-a-digest"
        malformed = attestation.with_record_identity(malformed)
        with self.assertRaisesRegex(
            core.ValidationError, "source evidence: malformed SHA-256"
        ):
            comparison_attestations.verify_attestation_record(malformed)

    def test_native_oracle_policy_requires_complete_matching_edges(self) -> None:
        manifest = comparison_attestations.build_attestation_manifest(
            [
                self.record(candidate="lcnf"),
                self.record(candidate="v8"),
            ]
        )
        summary = comparison_attestations.verify_oracle_policy(
            manifest,
            self.policy(),
        )
        self.assertEqual(summary["oracle"], "native")
        self.assertEqual(summary["requiredCandidates"], ["lcnf", "v8"])
        self.assertEqual(summary["selectedCaseCount"], 2)
        self.assertEqual(summary["comparisonCount"], 4)
        self.assertEqual(summary["witnessCount"], 4)
        self.assertEqual(
            summary["sourceEvidenceSha256"],
            self.source_evidence_sha256,
        )
        self.assertEqual(
            summary["sourceMatrixSha256"],
            self.source_matrix_sha256,
        )

        with self.assertRaisesRegex(
            core.ValidationError, "missing required edge native->v8"
        ):
            comparison_attestations.verify_oracle_policy(
                comparison_attestations.build_attestation_manifest(
                    [self.record(candidate="lcnf")]
                ),
                self.policy(),
            )

        with self.assertRaisesRegex(
            core.ValidationError, "edge does not match: native->v8"
        ):
            comparison_attestations.verify_oracle_policy(
                comparison_attestations.build_attestation_manifest(
                    [
                        self.record(candidate="lcnf"),
                        self.record(
                            candidate="v8",
                            equal=(True, False),
                        ),
                    ]
                ),
                self.policy(),
            )

        with self.assertRaisesRegex(
            core.ValidationError, "disagree on their matrix"
        ):
            comparison_attestations.verify_oracle_policy(
                comparison_attestations.build_attestation_manifest(
                    [
                        self.record(candidate="lcnf"),
                        self.record(
                            candidate="v8",
                            run_sha256="3" * 64,
                        ),
                    ]
                ),
                self.policy(),
            )

        with self.assertRaisesRegex(
            core.ValidationError, "share one immutable source snapshot"
        ):
            comparison_attestations.verify_oracle_policy(
                comparison_attestations.build_attestation_manifest(
                    [
                        self.record(candidate="lcnf"),
                        self.record(
                            candidate="v8",
                            source_evidence_sha256="6" * 64,
                        ),
                    ]
                ),
                self.policy(),
            )

        with self.assertRaisesRegex(
            core.ValidationError, "fewer than 3"
        ):
            comparison_attestations.verify_oracle_policy(
                manifest,
                self.policy(minimum_cases=3),
            )


class DirectNativeIrTests(unittest.TestCase):
    def attest_records(self, *args, **kwargs) -> tuple[list[dict], list[str]]:
        manifest, failures = native_ir.attest_artifacts(*args, **kwargs)
        return manifest["records"], failures

    def native_ir_descriptor(self, digest: str) -> dict:
        return {
            "version": 3,
            "caseId": "native-ir-case",
            "entry": "Fir.Validation.nativeIrCase",
            "dependencies": ["Fir.Validation.nativeIrHelper"],
            "claim": "the native helper takes the intended ownership path",
            "requiredArtifactFragments": ["return"],
            "requiredOwnershipFacts": [],
            "requiredOwnershipFactCounts": [
                {
                    "fact": "declaration:nativeIrCase",
                    "minimum": 1,
                    "maximum": 1,
                }
            ],
            "expectedArtifactSha256": digest,
        }

    def direct_descriptor(self) -> dict:
        return {
            "id": "native-ir-case",
            "requiredExecutedLcnfFormTrace": ["reset", "reuse"],
            "requiredExecutedLcnfFormCounts": [
                {"form": "reset", "minimum": 1, "maximum": 1},
                {"form": "reuse", "minimum": 1, "maximum": 1},
            ],
            "requiredAdministrativeStepKinds": ["admin:yield-cache"],
        }

    def direct_lcnf_result(self, value: int = 42) -> dict:
        record = success("native-ir-case", "direct-lcnf", value)
        record["diagnostics"] = [
            {
                "key": "executed-lcnf-form-trace",
                "value": json.dumps(["reset", "reuse"]),
            },
            {
                "key": "executed-lcnf-form-counts",
                "value": json.dumps(
                    [
                        {"form": "reset", "count": 1},
                        {"form": "reuse", "count": 1},
                    ]
                ),
            },
            {
                "key": "executed-step-trace",
                "value": json.dumps(
                    [
                        "admin:invoke-name",
                        "form:reset",
                        "form:reuse",
                        "admin:yield-cache",
                        "admin:yield-done",
                    ]
                ),
            },
            {"key": "interpreter-steps", "value": "5"},
        ]
        return record

    def test_native_ir_manifest_is_strict_and_preserves_roots(self) -> None:
        artifact = b"def nativeIrCase := return\n"
        descriptor = self.native_ir_descriptor(native_ir.sha256_bytes(artifact))
        parsed = native_ir.parse_manifest(
            json.dumps(descriptor) + "\n",
            ["fir-direct-native", "--native-oracle-manifest"],
        )
        self.assertEqual(parsed, [descriptor])

        duplicate = "\n".join([json.dumps(descriptor), json.dumps(descriptor)])
        with self.assertRaisesRegex(
            core.ValidationError, "duplicate native IR attestation case"
        ):
            native_ir.parse_manifest(duplicate, ["native-ir-manifest"])

        malformed = {**descriptor, "expectedArtifactSha256": "not-a-digest"}
        with self.assertRaisesRegex(core.ValidationError, "SHA-256"):
            native_ir.parse_manifest(json.dumps(malformed), ["native-ir-manifest"])

        malformed_claim = {**descriptor, "claim": " "}
        with self.assertRaisesRegex(core.ValidationError, "nonempty single line"):
            native_ir.parse_manifest(
                json.dumps(malformed_claim), ["native-ir-manifest"]
            )

        malformed_fragments = {
            **descriptor,
            "requiredArtifactFragments": ["return", "return"],
        }
        with self.assertRaisesRegex(core.ValidationError, "unique nonempty strings"):
            native_ir.parse_manifest(
                json.dumps(malformed_fragments), ["native-ir-manifest"]
            )

        malformed_facts = {
            **descriptor,
            "requiredOwnershipFacts": ["isShared:owner", "isShared:owner"],
        }
        with self.assertRaisesRegex(core.ValidationError, "ownership facts"):
            native_ir.parse_manifest(
                json.dumps(malformed_facts), ["native-ir-manifest"]
            )

        malformed_count_names = {
            **descriptor,
            "requiredOwnershipFactCounts": [
                {"fact": "isShared:owner", "minimum": 1, "maximum": 1},
                {"fact": "isShared:owner", "minimum": 2, "maximum": 2},
            ],
        }
        with self.assertRaisesRegex(
            core.ValidationError, "count names must be unique"
        ):
            native_ir.parse_manifest(
                json.dumps(malformed_count_names), ["native-ir-manifest"]
            )

        malformed_count_bounds = {
            **descriptor,
            "requiredOwnershipFactCounts": [
                {
                    "fact": "isShared:owner",
                    "minimum": 2,
                    "maximum": 1,
                }
            ],
        }
        with self.assertRaisesRegex(core.ValidationError, "bounds are invalid"):
            native_ir.parse_manifest(
                json.dumps(malformed_count_bounds), ["native-ir-manifest"]
            )

    def test_native_ir_attestation_records_evidence_and_mismatch(self) -> None:
        artifact = b"def nativeIrCase := return\n"
        digest = native_ir.sha256_bytes(artifact)
        descriptor = self.native_ir_descriptor(digest)
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            case_dir = out_dir / descriptor["caseId"]
            case_dir.mkdir()
            (case_dir / "program.lcnf").write_bytes(artifact)
            (case_dir / "entry.txt").write_text(
                descriptor["entry"] + "\n", encoding="utf-8"
            )
            (case_dir / "declarations.txt").write_text(
                "\n".join(
                    [descriptor["entry"], *descriptor["dependencies"], ""]
                ),
                encoding="utf-8",
            )
            (case_dir / "forms.txt").write_text(
                "return\n", encoding="utf-8"
            )

            direct_path = {"matches": True, "observationMatches": True}
            manifest, failures = native_ir.attest_artifacts(
                [descriptor],
                out_dir,
                direct_path_evidence_by_id={
                    descriptor["caseId"]: direct_path
                },
            )
            records = manifest["records"]
            self.assertEqual(failures, [])
            self.assertTrue(records[0]["matches"])
            self.assertEqual(records[0]["directPath"], direct_path)
            self.assertEqual(records[0]["artifactSha256"], digest)
            self.assertEqual(records[0]["claim"], descriptor["claim"])
            self.assertTrue(records[0]["claimMatches"])
            self.assertEqual(records[0]["missingArtifactFragments"], [])
            self.assertTrue(records[0]["ownershipMatches"])
            self.assertEqual(records[0]["missingOwnershipFacts"], [])
            self.assertTrue(records[0]["ownershipFactCountsMatch"])
            self.assertEqual(
                records[0]["observedOwnershipFactCounts"],
                [{"fact": "declaration:nativeIrCase", "count": 1}],
            )
            self.assertEqual(records[0]["unsatisfiedOwnershipFactCounts"], [])
            self.assertTrue((case_dir / "attestation.json").is_file())
            self.assertTrue((out_dir / "attestations.json").is_file())
            self.assertEqual(
                native_ir.verify_attestation_manifest(
                    out_dir / "attestations.json"
                ),
                manifest,
            )
            contract_sha256 = manifest["identity"]["contract"]
            evidence_sha256 = manifest["identity"]["evidence"]
            retained = (
                out_dir
                / "evidence"
                / "runs"
                / contract_sha256
                / f"{evidence_sha256}.json"
            )
            self.assertEqual(
                native_ir.verify_attestation_manifest(retained), manifest
            )
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(
                    native_ir.main(
                        ["--verify-attestations", str(retained)]
                    ),
                    0,
                )
            self.assertIn(evidence_sha256, stdout.getvalue())
            self.assertIn(contract_sha256, stdout.getvalue())

            second_record = dict(records[0])
            second_record.pop("identity")
            second_record["caseId"] = "z-native-ir-case"
            second_record["entry"] = "Fir.Validation.zNativeIrCase"
            second_record["dependencies"] = [
                "Fir.Validation.zNativeIrHelper"
            ]
            second_record["declarations"] = [
                second_record["entry"],
                *second_record["dependencies"],
            ]
            second_record = attestation.with_record_identity(second_record)
            ordered_manifest = native_ir.build_attestation_manifest(
                [second_record, records[0]]
            )
            self.assertEqual(
                [
                    record["caseId"]
                    for record in ordered_manifest["records"]
                ],
                ["native-ir-case", "z-native-ir-case"],
            )
            self.assertEqual(
                ordered_manifest,
                native_ir.build_attestation_manifest(
                    [records[0], second_record]
                ),
            )
            with self.assertRaisesRegex(
                core.ValidationError, "repeats a record ID"
            ):
                native_ir.build_attestation_manifest(
                    [records[0], records[0]]
                )

            tampered_evidence = json.loads(json.dumps(manifest))
            tampered_evidence["records"][0]["ownershipInventory"][
                "facts"
            ].append("tampered")
            with self.assertRaisesRegex(
                core.ValidationError, "record identity does not match"
            ):
                native_ir.verify_attestation_manifest_value(tampered_evidence)

            provisional_record = dict(tampered_evidence["records"][0])
            provisional_record.pop("identity")
            tampered_evidence["records"][0] = (
                attestation.with_record_identity(provisional_record)
            )
            with self.assertRaisesRegex(
                core.ValidationError, "ownership inventory derivatives disagree"
            ):
                native_ir.verify_attestation_manifest_value(tampered_evidence)

            tampered_evidence = json.loads(json.dumps(manifest))
            provisional_record = dict(tampered_evidence["records"][0])
            provisional_record.pop("identity")
            provisional_record["artifactBytes"] += 1
            tampered_evidence["records"][0] = (
                attestation.with_record_identity(provisional_record)
            )
            with self.assertRaisesRegex(
                core.ValidationError, "evidence identity does not match"
            ):
                native_ir.verify_attestation_manifest_value(tampered_evidence)

            tampered_contract = json.loads(json.dumps(manifest))
            provisional_record = dict(tampered_contract["records"][0])
            provisional_record.pop("identity")
            provisional_record["claim"] = "a different ownership claim"
            tampered_contract["records"][0] = (
                attestation.with_record_identity(provisional_record)
            )
            with self.assertRaisesRegex(
                core.ValidationError, "contract identity does not match"
            ):
                native_ir.verify_attestation_manifest_value(tampered_contract)

            records, failures = self.attest_records(
                [descriptor],
                out_dir,
                direct_path_evidence_by_id={
                    descriptor["caseId"]: {
                        "matches": False,
                        "failures": ["direct structural mismatch"],
                    }
                },
            )
            self.assertFalse(records[0]["matches"])
            self.assertEqual(failures, ["direct structural mismatch"])

            missing_claim = {
                **descriptor,
                "requiredArtifactFragments": ["isShared owner"],
            }
            records, failures = self.attest_records(
                [missing_claim], out_dir, verify_digest=False
            )
            self.assertFalse(records[0]["claimMatches"])
            self.assertTrue(records[0]["artifactMatches"])
            self.assertFalse(records[0]["matches"])
            self.assertEqual(len(failures), 1)

            missing_ownership = {
                **descriptor,
                "requiredOwnershipFacts": ["isShared:owner"],
            }
            records, failures = self.attest_records(
                [missing_ownership], out_dir, verify_digest=False
            )
            self.assertFalse(records[0]["ownershipMatches"])
            self.assertEqual(
                records[0]["missingOwnershipFacts"], ["isShared:owner"]
            )
            self.assertEqual(len(failures), 1)

            missing_ownership_count = {
                **descriptor,
                "requiredOwnershipFactCounts": [
                    {
                        "fact": "isShared:owner",
                        "minimum": 1,
                        "maximum": 1,
                    }
                ],
            }
            records, failures = self.attest_records(
                [missing_ownership_count], out_dir, verify_digest=False
            )
            self.assertEqual(
                records[0]["observedOwnershipFactCounts"],
                [{"fact": "isShared:owner", "count": 0}],
            )
            self.assertEqual(
                records[0]["unsatisfiedOwnershipFactCounts"],
                [
                    {
                        "fact": "isShared:owner",
                        "minimum": 1,
                        "maximum": 1,
                        "observed": 0,
                    }
                ],
            )
            self.assertRegex(failures[0], r"isShared:owner=0<1")

            wrong_ownership_count = {
                **descriptor,
                "requiredOwnershipFactCounts": [
                    {
                        "fact": "declaration:nativeIrCase",
                        "minimum": 0,
                        "maximum": 0,
                    }
                ],
            }
            records, failures = self.attest_records(
                [wrong_ownership_count], out_dir, verify_digest=False
            )
            self.assertFalse(records[0]["ownershipFactCountsMatch"])
            self.assertFalse(records[0]["ownershipMatches"])
            self.assertEqual(
                records[0]["unsatisfiedOwnershipFactCounts"],
                [
                    {
                        "fact": "declaration:nativeIrCase",
                        "minimum": 0,
                        "maximum": 0,
                        "observed": 1,
                    }
                ],
            )
            self.assertRegex(failures[0], r"declaration:nativeIrCase=1>0")

            mismatch = {
                **descriptor,
                "expectedArtifactSha256": "0" * 64,
            }
            records, failures = self.attest_records(
                [mismatch], out_dir, verify_digest=False
            )
            self.assertFalse(records[0]["artifactMatches"])
            self.assertTrue(records[0]["claimMatches"])
            self.assertEqual(failures, [])

            records, failures = self.attest_records(
                [mismatch], out_dir
            )
            self.assertFalse(records[0]["matches"])
            self.assertEqual(len(failures), 1)

    def test_native_ir_attestation_rejects_missing_root(self) -> None:
        artifact = b"def nativeIrCase := return\n"
        descriptor = self.native_ir_descriptor(native_ir.sha256_bytes(artifact))
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            case_dir = out_dir / descriptor["caseId"]
            case_dir.mkdir()
            (case_dir / "program.lcnf").write_bytes(artifact)
            (case_dir / "entry.txt").write_text(
                descriptor["entry"] + "\n", encoding="utf-8"
            )
            (case_dir / "declarations.txt").write_text(
                descriptor["entry"] + "\n", encoding="utf-8"
            )
            (case_dir / "forms.txt").write_text(
                "return\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(
                core.ValidationError, "omits rooted declarations"
            ):
                native_ir.attest_artifacts([descriptor], out_dir)

    def test_direct_path_evidence_binds_observation_and_machine_trace(self) -> None:
        descriptor = self.direct_descriptor()
        native_result = success("native-ir-case", "direct-native")
        lcnf_result = self.direct_lcnf_result()
        evidence, failures = native_ir.direct_path_evidence(
            descriptor,
            native_result,
            lcnf_result,
        )
        self.assertEqual(failures, [])
        self.assertTrue(evidence["matches"])
        self.assertTrue(evidence["observationMatches"])
        self.assertTrue(evidence["formTraceMatches"])
        self.assertTrue(evidence["formCountsMatchTrace"])
        self.assertTrue(evidence["stepFormsMatch"])
        self.assertTrue(evidence["stepCountMatches"])
        self.assertEqual(evidence["missingAdministrativeStepKinds"], [])

        changed_result = self.direct_lcnf_result(43)
        evidence, failures = native_ir.direct_path_evidence(
            descriptor,
            native_result,
            changed_result,
        )
        self.assertFalse(evidence["matches"])
        self.assertFalse(evidence["observationMatches"])
        self.assertEqual(len(failures), 1)

        changed_trace = self.direct_lcnf_result()
        changed_trace["diagnostics"][0]["value"] = json.dumps(
            ["reuse", "reset"]
        )
        evidence, failures = native_ir.direct_path_evidence(
            descriptor,
            native_result,
            changed_trace,
        )
        self.assertFalse(evidence["matches"])
        self.assertFalse(evidence["formTraceMatches"])
        self.assertFalse(evidence["stepFormsMatch"])
        self.assertEqual(evidence["failures"], failures)

    def test_ownership_inventory_normalizes_reference_count_paths(self) -> None:
        artifact = """
  let child := ctor_0[Example.NativeHeapChild.mk] first second;
  inc[2][ref] child;
  inc[persistent][ref] owner;
  let isSharedCheck.7 := isShared owner;
  let unused.9 := oproj[1] owner;
  dec unused.9;
  oset _x.2 [1] := marker;
def second : obj :=
  dec unused.9;
  return owner
"""
        inventory = native_ir.ownership_inventory(artifact)
        self.assertEqual(inventory["unknownAttributes"], [])
        self.assertEqual(
            set(inventory["facts"]),
            {
                "ctor:NativeHeapChild.mk",
                "inc:child:amount=2:persistent=false:reference=true",
                "inc:owner:amount=1:persistent=true:reference=true",
                "isShared:owner",
                "project:owner:index=1",
                "dec:unused:reference=false",
                "project-dec:owner:index=1",
                "oset:index=1",
                "declaration:second",
            },
        )
        fact_counts = {
            item["fact"]: item["count"] for item in inventory["factCounts"]
        }
        self.assertEqual(fact_counts["project-dec:owner:index=1"], 1)
        unknown = native_ir.ownership_inventory("  inc[mystery] owner;\n")
        self.assertEqual(unknown["unknownAttributes"], ["mystery"])


class CoverageIndexTests(unittest.TestCase):
    @staticmethod
    def matrix(
        case_ids: list[str],
        backends: list[str],
        pairs: list[tuple[str, str]],
    ) -> dict:
        return {
            "version": 3,
            "identity": {
                "algorithm": "sha256",
                "run": "1" * 64,
                "selection": "2" * 64,
            },
            "backends": backends,
            "selectedCases": case_ids,
            "pairs": [
                {
                    "reference": reference,
                    "candidate": candidate,
                    "artifact": f"evidence/{reference}-{candidate}",
                    "sha256": "3" * 64,
                    "comparedCases": len(case_ids),
                    "equalCases": len(case_ids),
                    "findingCount": 0,
                }
                for reference, candidate in pairs
            ],
            "coverage": {
                "findingCount": 0,
                "backends": [
                    {
                        "backend": backend,
                        "selectedCaseCount": len(case_ids),
                        "resultCaseCount": len(case_ids),
                        "successfulCaseCount": len(case_ids),
                        "comparisonCount": len(case_ids),
                        "equalComparisonCount": len(case_ids),
                        "findingCount": 0,
                    }
                    for backend in backends
                ],
                "providers": [],
                "consumers": [],
            },
        }

    @staticmethod
    def machine_report(
        backend: str,
        case_ids: list[str],
        *,
        form: str = "return",
        administrative_kind: str = "admin:yield-done",
        unobserved_kinds: list[str] | None = None,
    ) -> dict:
        case_count = len(case_ids)
        return {
            "version": 3,
            "backend": backend,
            "caseCount": case_count,
            "cases": [{"caseId": case_id} for case_id in case_ids],
            "summary": {
                "static": {
                    "observedForms": [form],
                    "requiredForms": [form],
                    "missingObligationCount": 0,
                },
                "executed": {
                    "casesWithDiagnostics": case_count,
                    "casesWithRequirements": case_count,
                    "observedForms": [form],
                    "requiredForms": [form],
                    "missingObligationCount": 0,
                    "totalInterpreterSteps": case_count * 2,
                    "formCounts": {
                        "casesWithValidDiagnostics": case_count,
                        "observed": [{"form": form, "count": case_count}],
                        "requiredMinimums": [
                            {"form": form, "minimum": case_count}
                        ],
                        "unsatisfiedObligationCount": 0,
                    },
                    "formTrace": {
                        "casesWithValidDiagnostics": case_count,
                        "mismatchedObligationCount": 0,
                    },
                    "stepTrace": {
                        "casesWithValidDiagnostics": case_count,
                        "casesWithCompleteCoverage": case_count,
                        "administrativeKinds": [
                            {
                                "kind": administrative_kind,
                                "count": case_count,
                            }
                        ],
                        "requiredAdministrativeKinds": [administrative_kind],
                        "unobservedAdministrativeKinds": (
                            unobserved_kinds or []
                        ),
                        "missingAdministrativeObligationCount": 0,
                        "unclassifiedStepCount": 0,
                    },
                },
                "externals": {
                    "static": {
                        "observedNames": [],
                        "requiredNames": [],
                        "missingObligationCount": 0,
                    },
                    "executed": {
                        "observedNames": [],
                        "requiredNames": [],
                        "missingObligationCount": 0,
                        "counts": {
                            "casesWithValidDiagnostics": case_count,
                            "observed": [],
                            "requiredMinimums": [],
                            "unsatisfiedObligationCount": 0,
                        },
                        "trace": {
                            "casesWithValidDiagnostics": case_count,
                            "mismatchedObligationCount": 0,
                        },
                    },
                },
            },
        }

    @staticmethod
    def policy(
        tier_id: str,
        backends: list[str],
        *,
        minimum_cases: int = 1,
        minimum_comparisons: int = 1,
        require_machine: bool = True,
    ) -> dict:
        return {
            "tiers": [
                {
                    "id": tier_id,
                    "minimumCases": minimum_cases,
                    "minimumComparisons": minimum_comparisons,
                    "requiredBackends": sorted(backends),
                    "requireMachineCoverage": require_machine,
                }
            ],
            "aggregate": {
                "minimumUniqueCases": minimum_cases,
                "minimumTierCases": minimum_cases,
                "minimumComparisons": minimum_comparisons,
            },
            "machine": {
                "minimumCases": minimum_cases if require_machine else 0,
                "minimumInterpreterSteps": (
                    minimum_cases * 2 if require_machine else 0
                ),
                "requiredStaticForms": ["return"] if require_machine else [],
                "requiredExecutedForms": ["return"] if require_machine else [],
                "requiredAdministrativeKinds": (
                    ["admin:yield-done"] if require_machine else []
                ),
                "requiredExternals": [],
            },
            "semanticTags": [],
            "semanticDomains": [],
        }

    def test_machine_coverage_requires_the_matrix_case_domain(self) -> None:
        matrix = self.matrix(["a"], ["native", "lcnf"], [("native", "lcnf")])
        report = self.machine_report("lcnf", ["b"])
        with self.assertRaisesRegex(
            core.ValidationError, "case domain disagrees"
        ):
            coverage_index.machine_coverage_summary(report, matrix, "fixture")

    def test_machine_coverage_aggregate_closes_cross_tier_admin_gap(self) -> None:
        source_matrix = self.matrix(
            ["source"], ["native", "lcnf"], [("native", "lcnf")]
        )
        direct_matrix = self.matrix(
            ["direct"],
            ["direct-native", "direct-lcnf"],
            [("direct-native", "direct-lcnf")],
        )
        source = coverage_index.machine_coverage_summary(
            self.machine_report(
                "lcnf",
                ["source"],
                administrative_kind="admin:yield-done",
                unobserved_kinds=["admin:yield-apply"],
            ),
            source_matrix,
            "source",
        )
        direct = coverage_index.machine_coverage_summary(
            self.machine_report(
                "direct-lcnf",
                ["direct"],
                administrative_kind="admin:yield-apply",
            ),
            direct_matrix,
            "direct",
        )
        aggregate = coverage_index.aggregate_machine_coverage([source, direct])
        self.assertEqual(aggregate["caseCount"], 2)
        self.assertEqual(
            aggregate["steps"]["observedAdministrativeKinds"],
            [
                {"kind": "admin:yield-apply", "count": 1},
                {"kind": "admin:yield-done", "count": 1},
            ],
        )
        self.assertEqual(
            aggregate["steps"]["unobservedAdministrativeKinds"], []
        )
        self.assertTrue(aggregate["complete"])
        attribution = coverage_index.coverage_attribution(
            [
                {
                    "id": "source",
                    "caseIds": ["source"],
                    "machineCoverage": source,
                },
                {
                    "id": "direct",
                    "caseIds": ["direct"],
                    "machineCoverage": direct,
                },
            ],
            {
                "machine": {
                    "requiredStaticForms": ["return"],
                    "requiredExecutedForms": ["return"],
                    "requiredAdministrativeKinds": [
                        "admin:yield-apply",
                        "admin:yield-done",
                    ],
                    "requiredExternals": [],
                }
            },
        )
        apply_attribution = next(
            item
            for item in attribution["administrativeKinds"]["items"]
            if item["name"] == "admin:yield-apply"
        )
        self.assertEqual(apply_attribution["tiers"], ["direct"])
        self.assertTrue(apply_attribution["uniqueContribution"])
        self.assertEqual(
            attribution["tiers"][1]["uniqueContributions"]["cases"],
            ["direct"],
        )
        self.assertTrue(attribution["summary"]["complete"])

    def test_index_is_deterministic_and_verifies_current_inputs(self) -> None:
        matrix = self.matrix(["case"], ["native", "lcnf"], [("native", "lcnf")])
        machine = self.machine_report("lcnf", ["case"])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_dir = root / "validation-plans"
            build_dir = root / "_build" / "source"
            plan_dir.mkdir()
            build_dir.mkdir(parents=True)
            matrix_path = build_dir / "matrix.json"
            coverage_path = build_dir / "coverage.json"
            matrix_path.write_bytes(json_bytes(matrix))
            coverage_path.write_bytes(json_bytes(machine))
            plan = {
                "version": 3,
                "tiers": [
                    {
                        "id": "source",
                        "kind": "source-compiled",
                        "matrix": "../_build/source/matrix.json",
                        "pairs": [
                            {"reference": "native", "candidate": "lcnf"}
                        ],
                        "machineCoverage": "../_build/source/coverage.json",
                    }
                ],
                "policy": self.policy(
                    "source", ["native", "lcnf"]
                ),
            }
            plan_path = plan_dir / "coverage-index.json"
            plan_path.write_bytes(json_bytes(plan))
            with mock.patch.object(
                coverage_index,
                "verify_matrix_artifact",
                return_value=matrix,
            ):
                first = coverage_index.build_coverage_index(plan_path, root)
                second = coverage_index.build_coverage_index(plan_path, root)
                self.assertEqual(first, second)
                index_path = root / "_build" / "index.json"
                coverage_index.write_coverage_index(index_path, first)
                self.assertEqual(
                    coverage_index.verify_coverage_index(index_path, root),
                    first,
                )
        self.assertEqual(first["summary"]["comparisonCount"], 1)
        self.assertEqual(first["summary"]["machine"]["caseCount"], 1)
        self.assertEqual(first["summary"]["policyFailureCount"], 0)
        self.assertEqual(
            first["summary"]["attributionUncoveredRequiredItemCount"], 0
        )
        self.assertTrue(first["policy"]["satisfied"])
        self.assertTrue(first["attribution"]["summary"]["complete"])
        self.assertTrue(first["summary"]["complete"])

    def test_verified_index_comparison_reports_gains_and_regressions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_dir = root / "validation-plans"
            build_dir = root / "_build"
            plan_dir.mkdir()
            build_dir.mkdir()
            matrix_path = build_dir / "matrix.json"
            plan = {
                "version": 3,
                "tiers": [
                    {
                        "id": "source",
                        "kind": "source-compiled",
                        "matrix": "../_build/matrix.json",
                        "pairs": [
                            {"reference": "native", "candidate": "lcnf"}
                        ],
                        "machineCoverage": None,
                    }
                ],
                "policy": self.policy(
                    "source",
                    ["native", "lcnf"],
                    require_machine=False,
                ),
            }
            plan_path = plan_dir / "coverage-index.json"
            plan_path.write_bytes(json_bytes(plan))

            def build(case_ids: list[str]) -> dict:
                matrix = self.matrix(
                    case_ids,
                    ["native", "lcnf"],
                    [("native", "lcnf")],
                )
                matrix_path.write_bytes(json_bytes(matrix))
                with mock.patch.object(
                    coverage_index,
                    "verify_matrix_artifact",
                    return_value=matrix,
                ):
                    return coverage_index.build_coverage_index(
                        plan_path, root
                    )

            before = build(["case"])
            after = build(["case", "new-case"])
            snapshots = root / "relocated" / "snapshots"
            before_path = snapshots / "before.json"
            after_path = snapshots / "after.json"
            coverage_index.write_coverage_index(before_path, before)
            coverage_index.write_coverage_index(after_path, after)

            gain = coverage_index.compare_verified_coverage_indexes(
                before_path, after_path
            )
            regression = coverage_index.compare_verified_coverage_indexes(
                after_path, before_path
            )
            for before_cli, after_cli, expected_status in (
                (before_path, after_path, 0),
                (after_path, before_path, 1),
            ):
                with (
                    mock.patch.object(
                        sys,
                        "argv",
                        [
                            "validation_coverage_index.py",
                            "--compare-index",
                            str(before_cli),
                            str(after_cli),
                            "--require-no-regression",
                        ],
                    ),
                    contextlib.redirect_stdout(io.StringIO()),
                ):
                    self.assertEqual(
                        coverage_index.main(), expected_status
                    )
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "validation_coverage_index.py",
                        "--compare-index",
                        str(after_path),
                        str(before_path),
                    ],
                ),
                contextlib.redirect_stdout(io.StringIO()),
            ):
                self.assertEqual(coverage_index.main(), 0)

        self.assertTrue(gain["classification"]["coverageGained"])
        self.assertFalse(gain["classification"]["coverageRegressed"])
        self.assertFalse(gain["classification"]["regressionDetected"])
        self.assertEqual(gain["coverage"]["cases"]["added"], ["new-case"])
        self.assertEqual(gain["summary"]["observedItemAddedCount"], 1)
        self.assertGreater(gain["summary"]["policySlackIncreaseCount"], 0)
        self.assertEqual(
            set(gain["before"]), {"index", "plan"}
        )
        self.assertNotIn(
            "relocated",
            json.dumps(gain, sort_keys=True),
        )

        self.assertTrue(regression["classification"]["coverageRegressed"])
        self.assertTrue(regression["classification"]["regressionDetected"])
        self.assertEqual(
            regression["coverage"]["cases"]["removed"], ["new-case"]
        )
        self.assertEqual(
            regression["summary"]["observedItemRemovedCount"], 1
        )
        self.assertGreater(
            regression["summary"]["policySlackDecreaseCount"], 0
        )

    def test_no_regression_gate_requires_index_comparison(self) -> None:
        with mock.patch.object(
            sys,
            "argv",
            [
                "validation_coverage_index.py",
                "--require-no-regression",
            ],
        ):
            with self.assertRaisesRegex(
                core.ValidationError,
                "--require-no-regression requires --compare-index",
            ):
                coverage_index.main()

    def test_snapshot_verification_recomputes_derived_claims(self) -> None:
        matrix = self.matrix(
            ["case"], ["native", "lcnf"], [("native", "lcnf")]
        )
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_dir = root / "validation-plans"
            build_dir = root / "_build"
            plan_dir.mkdir()
            build_dir.mkdir()
            matrix_path = build_dir / "matrix.json"
            matrix_path.write_bytes(json_bytes(matrix))
            plan = {
                "version": 3,
                "tiers": [
                    {
                        "id": "source",
                        "kind": "source-compiled",
                        "matrix": "../_build/matrix.json",
                        "pairs": [
                            {"reference": "native", "candidate": "lcnf"}
                        ],
                        "machineCoverage": None,
                    }
                ],
                "policy": self.policy(
                    "source",
                    ["native", "lcnf"],
                    require_machine=False,
                ),
            }
            plan_path = plan_dir / "coverage-index.json"
            plan_path.write_bytes(json_bytes(plan))
            with mock.patch.object(
                coverage_index,
                "verify_matrix_artifact",
                return_value=matrix,
            ):
                report = coverage_index.build_coverage_index(plan_path, root)
            tampered = json.loads(json.dumps(report))
            tampered["summary"]["uniqueCaseCount"] += 1
            provisional = dict(tampered)
            provisional.pop("identity")
            tampered["identity"]["index"] = (
                core.canonical_json_sha256(provisional)
            )
            path = root / "relocated.json"
            path.write_bytes(json_bytes(tampered))
            with self.assertRaisesRegex(
                core.ValidationError, "derivatives disagree"
            ):
                coverage_index.verify_coverage_index_snapshot(path)

    def test_index_comparison_tracks_attribution_and_new_policy_gaps(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_dir = root / "validation-plans"
            build_dir = root / "_build"
            plan_dir.mkdir()
            build_dir.mkdir()
            matrix_paths = {
                tier_id: build_dir / f"{tier_id}.json"
                for tier_id in ("source", "direct")
            }
            tier_requirements = [
                {
                    "id": tier_id,
                    "minimumCases": 1,
                    "minimumComparisons": 1,
                    "requiredBackends": ["lcnf", "native"],
                    "requireMachineCoverage": False,
                }
                for tier_id in ("source", "direct")
            ]
            plan = {
                "version": 3,
                "tiers": [
                    {
                        "id": tier_id,
                        "kind": f"{tier_id}-kind",
                        "matrix": f"../_build/{tier_id}.json",
                        "pairs": [
                            {"reference": "native", "candidate": "lcnf"}
                        ],
                        "machineCoverage": None,
                    }
                    for tier_id in ("source", "direct")
                ],
                "policy": {
                    "tiers": tier_requirements,
                    "aggregate": {
                        "minimumUniqueCases": 2,
                        "minimumTierCases": 2,
                        "minimumComparisons": 2,
                    },
                    "machine": {
                        "minimumCases": 0,
                        "minimumInterpreterSteps": 0,
                        "requiredStaticForms": [],
                        "requiredExecutedForms": [],
                        "requiredAdministrativeKinds": [],
                        "requiredExternals": [],
                    },
                    "semanticTags": [],
                    "semanticDomains": [],
                },
            }
            plan_path = plan_dir / "coverage-index.json"

            def build(source_cases: list[str], direct_cases: list[str]) -> dict:
                for tier_id, case_ids in (
                    ("source", source_cases),
                    ("direct", direct_cases),
                ):
                    matrix_paths[tier_id].write_bytes(
                        json_bytes(
                            self.matrix(
                                case_ids,
                                ["native", "lcnf"],
                                [("native", "lcnf")],
                            )
                        )
                    )
                plan_path.write_bytes(json_bytes(plan))
                with mock.patch.object(
                    coverage_index,
                    "verify_matrix_artifact",
                    side_effect=lambda path: json.loads(
                        Path(path).read_text(encoding="utf-8")
                    ),
                ):
                    return coverage_index.build_coverage_index(
                        plan_path, root
                    )

            before = build(["shared"], ["direct-only"])
            shared = build(
                ["shared"], ["direct-only", "shared"]
            )
            attribution_gain = coverage_index.compare_coverage_indexes(
                before, shared
            )
            attribution_loss = coverage_index.compare_coverage_indexes(
                shared, before
            )

            plan["policy"]["machine"]["requiredStaticForms"] = ["return"]
            strict = build(["shared"], ["direct-only"])
            policy_gap = coverage_index.compare_coverage_indexes(
                before, strict
            )

        shared_change = attribution_gain["coverage"]["cases"][
            "attributionChanged"
        ]
        self.assertEqual(
            shared_change,
            [
                {
                    "name": "shared",
                    "beforeTiers": ["source"],
                    "afterTiers": ["source", "direct"],
                    "addedTiers": ["direct"],
                    "removedTiers": [],
                }
            ],
        )
        self.assertEqual(
            attribution_gain["summary"]["observedItemAddedCount"], 0
        )
        self.assertTrue(attribution_gain["classification"]["coverageGained"])
        self.assertFalse(
            attribution_gain["classification"]["coverageRegressed"]
        )
        self.assertEqual(
            attribution_loss["summary"]["attributionTierLossCount"], 1
        )
        self.assertTrue(
            attribution_loss["classification"]["regressionDetected"]
        )

        static_forms = policy_gap["coverage"]["staticForms"]
        self.assertEqual(static_forms["policyAdded"], ["return"])
        self.assertEqual(
            static_forms["newlyUncoveredRequired"], ["return"]
        )
        self.assertTrue(
            policy_gap["classification"]["policyRequirementsChanged"]
        )
        self.assertTrue(
            policy_gap["classification"]["policyFailuresIncreased"]
        )
        self.assertTrue(policy_gap["classification"]["regressionDetected"])

    def test_policy_reports_monotone_floor_and_inventory_regressions(self) -> None:
        matrix = self.matrix(
            ["case"], ["native", "lcnf"], [("native", "lcnf")]
        )
        machine = coverage_index.machine_coverage_summary(
            self.machine_report("lcnf", ["case"]),
            matrix,
            "fixture",
        )
        tier = {
            "id": "source",
            "caseIds": ["case"],
            "caseCount": 1,
            "backends": [{"backend": "native"}, {"backend": "lcnf"}],
            "pairs": [{"comparedCases": 1}],
            "machineCoverage": machine,
        }
        aggregate = coverage_index.aggregate_machine_coverage([machine])
        summary = {
            "uniqueCaseCount": 1,
            "tierCaseCount": 1,
            "comparisonCount": 1,
            "machine": aggregate,
        }
        policy = self.policy(
            "source",
            ["native", "lcnf"],
            minimum_cases=2,
            minimum_comparisons=2,
        )
        policy["machine"]["requiredAdministrativeKinds"] = [
            "admin:yield-apply",
            "admin:yield-done",
        ]
        report = coverage_index.coverage_policy_report(
            policy, [tier], summary
        )
        self.assertEqual(report["failureCount"], 8)
        self.assertEqual(report["tiers"][0]["caseDeficit"], 1)
        self.assertEqual(report["aggregate"]["comparisonDeficit"], 1)
        self.assertEqual(
            report["machine"]["missingAdministrativeKinds"],
            ["admin:yield-apply"],
        )
        self.assertFalse(report["satisfied"])
        attribution = coverage_index.coverage_attribution([tier], report)
        apply_attribution = next(
            item
            for item in attribution["administrativeKinds"]["items"]
            if item["name"] == "admin:yield-apply"
        )
        self.assertEqual(apply_attribution["tiers"], [])
        self.assertEqual(
            attribution["summary"]["uncoveredRequiredItemCount"], 1
        )
        self.assertFalse(attribution["summary"]["complete"])

    def test_semantic_tag_policy_uses_selected_retained_corpus_cases(self) -> None:
        descriptors = [
            descriptor("arithmetic-case", tags=["arithmetic", "quick"]),
            descriptor("ownership-case", tags=["ownership", "quick"]),
            descriptor(
                "shared-case",
                tags=["arithmetic", "ownership", "quick"],
            ),
        ]
        corpus_content = core.corpus_artifact_bytes(descriptors)
        corpus_digest = core.sha256_bytes(corpus_content)
        matrix = self.matrix(
            ["arithmetic-case", "shared-case"],
            ["native", "lcnf"],
            [("native", "lcnf")],
        )
        matrix["inputs"] = [
            {
                "kind": "corpus",
                "name": "corpus.json",
                "sha256": corpus_digest,
                "artifact": f"evidence/inputs/{corpus_digest}",
            }
        ]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            matrix_path = root / "matrix.json"
            corpus_path = root / "evidence" / "inputs" / corpus_digest
            corpus_path.parent.mkdir(parents=True)
            corpus_path.write_bytes(corpus_content)
            semantic = coverage_index.semantic_coverage_from_matrix(
                matrix_path, matrix, "fixture"
            )
        self.assertEqual(
            semantic,
            [
                {
                    "tag": "arithmetic",
                    "caseIds": ["arithmetic-case", "shared-case"],
                },
                {
                    "tag": "ownership",
                    "caseIds": ["shared-case"],
                },
                {
                    "tag": "quick",
                    "caseIds": ["arithmetic-case", "shared-case"],
                },
            ],
        )

        tier = {
            "id": "source",
            "caseIds": ["arithmetic-case", "shared-case"],
            "caseCount": 2,
            "backends": [{"backend": "native"}, {"backend": "lcnf"}],
            "pairs": [{"comparedCases": 2}],
            "machineCoverage": None,
            "semanticCoverage": semantic,
        }
        summary = {
            "uniqueCaseCount": 2,
            "tierCaseCount": 2,
            "comparisonCount": 2,
            "machine": coverage_index.aggregate_machine_coverage([]),
        }
        policy = self.policy(
            "source",
            ["native", "lcnf"],
            minimum_cases=2,
            minimum_comparisons=2,
            require_machine=False,
        )
        policy["semanticTags"] = [
            {"tier": "source", "tag": "arithmetic", "minimumCases": 2},
            {"tier": "source", "tag": "ownership", "minimumCases": 2},
        ]
        policy["semanticDomains"] = [
            {
                "tier": "source",
                "name": "arithmetic-ownership",
                "allTags": ["arithmetic", "ownership"],
                "minimumCases": 1,
            },
            {
                "tier": "source",
                "name": "arithmetic-quick",
                "allTags": ["arithmetic", "quick"],
                "minimumCases": 2,
            },
            {
                "tier": "source",
                "name": "ownership-quick",
                "allTags": ["ownership", "quick"],
                "minimumCases": 2,
            },
        ]
        report = coverage_index.coverage_policy_report(
            policy, [tier], summary
        )
        self.assertEqual(report["semanticTags"][0]["caseDeficit"], 0)
        self.assertEqual(report["semanticTags"][1]["caseDeficit"], 1)
        self.assertEqual(
            report["semanticDomains"][0]["caseIds"], ["shared-case"]
        )
        self.assertEqual(
            report["semanticDomains"][1]["caseIds"],
            ["arithmetic-case", "shared-case"],
        )
        self.assertEqual(report["semanticDomains"][2]["caseDeficit"], 1)
        self.assertEqual(report["failureCount"], 2)
        self.assertEqual(
            coverage_index.coverage_policy_declaration(report)[
                "semanticDomains"
            ],
            policy["semanticDomains"],
        )
        self.assertEqual(
            [
                item["cases"]
                for item in coverage_index.coverage_policy_slack(report)[
                    "semanticDomains"
                ]
            ],
            [0, 0, -1],
        )
        attribution = coverage_index.coverage_attribution([tier], report)
        self.assertEqual(
            attribution["semanticTags"]["summary"]["requiredItemCount"], 2
        )
        self.assertEqual(
            attribution["semanticTags"]["summary"][
                "coveredRequiredItemCount"
            ],
            2,
        )
        self.assertEqual(
            attribution["semanticDomains"]["summary"]["requiredItemCount"], 3
        )
        self.assertEqual(
            attribution["semanticDomains"]["summary"][
                "coveredRequiredItemCount"
            ],
            3,
        )

    def test_verified_index_comparison_detects_semantic_domain_loss(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_dir = root / "validation-plans"
            build_dir = root / "_build"
            plan_dir.mkdir()
            build_dir.mkdir()
            matrix_path = build_dir / "matrix.json"
            policy = self.policy(
                "source",
                ["native", "lcnf"],
                require_machine=False,
            )
            policy["semanticDomains"] = [
                {
                    "tier": "source",
                    "name": "arithmetic-ownership",
                    "allTags": ["arithmetic", "ownership"],
                    "minimumCases": 1,
                }
            ]
            plan = {
                "version": 3,
                "tiers": [
                    {
                        "id": "source",
                        "kind": "source-compiled",
                        "matrix": "../_build/matrix.json",
                        "pairs": [
                            {"reference": "native", "candidate": "lcnf"}
                        ],
                        "machineCoverage": None,
                    }
                ],
                "policy": policy,
            }
            plan_path = plan_dir / "coverage-index.json"
            plan_path.write_bytes(json_bytes(plan))

            def build(tags: list[str], snapshot_name: str) -> Path:
                corpus_content = core.corpus_artifact_bytes(
                    [descriptor("case", tags=tags)]
                )
                corpus_digest = core.sha256_bytes(corpus_content)
                corpus_path = (
                    build_dir / "evidence" / "inputs" / corpus_digest
                )
                corpus_path.parent.mkdir(parents=True, exist_ok=True)
                corpus_path.write_bytes(corpus_content)
                matrix = self.matrix(
                    ["case"],
                    ["native", "lcnf"],
                    [("native", "lcnf")],
                )
                matrix["inputs"] = [
                    {
                        "kind": "corpus",
                        "name": "corpus.json",
                        "sha256": corpus_digest,
                        "artifact": f"evidence/inputs/{corpus_digest}",
                    }
                ]
                matrix_path.write_bytes(json_bytes(matrix))
                with mock.patch.object(
                    coverage_index,
                    "verify_matrix_artifact",
                    return_value=matrix,
                ):
                    report = coverage_index.build_coverage_index(
                        plan_path, root
                    )
                snapshot_path = root / f"{snapshot_name}.json"
                coverage_index.write_coverage_index(snapshot_path, report)
                return snapshot_path

            before_path = build(
                ["arithmetic", "ownership"], "before"
            )
            after_path = build(["arithmetic"], "after")
            comparison = coverage_index.compare_verified_coverage_indexes(
                before_path, after_path
            )

        semantic_domains = comparison["coverage"]["semanticDomains"]
        self.assertEqual(
            semantic_domains["removed"],
            ["source:arithmetic-ownership"],
        )
        self.assertEqual(
            semantic_domains["newlyUncoveredRequired"],
            ["source:arithmetic-ownership"],
        )
        self.assertTrue(
            comparison["classification"]["coverageRegressed"]
        )
        self.assertTrue(
            comparison["classification"]["policyFailuresIncreased"]
        )
        self.assertTrue(
            comparison["classification"]["policySlackRegressed"]
        )
        self.assertTrue(
            comparison["classification"]["regressionDetected"]
        )

    def test_policy_rejects_ambiguous_required_inventories(self) -> None:
        policy = self.policy("source", ["native", "lcnf"])
        policy["machine"]["requiredExecutedForms"] = ["return", "return"]
        machine = coverage_index.aggregate_machine_coverage([])
        summary = {
            "uniqueCaseCount": 0,
            "tierCaseCount": 0,
            "comparisonCount": 0,
            "machine": machine,
        }
        tier = {
            "id": "source",
            "caseCount": 0,
            "backends": [],
            "pairs": [],
            "machineCoverage": None,
        }
        with self.assertRaisesRegex(
            core.ValidationError, "sorted array of unique"
        ):
            coverage_index.coverage_policy_report(
                policy, [tier], summary
            )

        policy = self.policy("source", ["native", "lcnf"])
        policy["semanticDomains"] = [
            {
                "tier": "source",
                "name": "not-conjunctive",
                "allTags": ["arithmetic"],
                "minimumCases": 1,
            }
        ]
        with self.assertRaisesRegex(
            core.ValidationError, "must require at least two tags"
        ):
            coverage_index.coverage_policy_report(
                policy, [tier], summary
            )

    def test_cli_fails_when_the_coverage_policy_is_unsatisfied(self) -> None:
        report = {"summary": {"complete": False}}
        with mock.patch.object(
            sys,
            "argv",
            [
                "validation_coverage_index.py",
                "--plan",
                "plan.json",
                "--out",
                "index.json",
            ],
        ), mock.patch.object(
            coverage_index,
            "build_coverage_index",
            return_value=report,
        ), mock.patch.object(
            coverage_index, "write_coverage_index"
        ), mock.patch.object(
            coverage_index, "render_coverage_index", return_value=[]
        ):
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(coverage_index.main(), 1)

    def test_index_rejects_a_pair_absent_from_the_matrix(self) -> None:
        matrix = self.matrix(["case"], ["native", "lcnf"], [("native", "lcnf")])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            plan_dir = root / "validation-plans"
            build_dir = root / "_build"
            plan_dir.mkdir()
            build_dir.mkdir()
            matrix_path = build_dir / "matrix.json"
            matrix_path.write_bytes(json_bytes(matrix))
            plan = {
                "version": 3,
                "tiers": [
                    {
                        "id": "source",
                        "kind": "source-compiled",
                        "matrix": "../_build/matrix.json",
                        "pairs": [
                            {"reference": "lcnf", "candidate": "native"}
                        ],
                        "machineCoverage": None,
                    }
                ],
                "policy": self.policy(
                    "source",
                    ["native", "lcnf"],
                    require_machine=False,
                ),
            }
            plan_path = plan_dir / "coverage-index.json"
            plan_path.write_bytes(json_bytes(plan))
            with mock.patch.object(
                coverage_index,
                "verify_matrix_artifact",
                return_value=matrix,
            ), self.assertRaisesRegex(
                core.ValidationError, "selects pairs absent"
            ):
                coverage_index.build_coverage_index(plan_path, root)

    def test_index_identity_detects_tampering(self) -> None:
        report = {
            "version": 3,
            "identity": {"algorithm": "sha256", "index": "0" * 64},
            "plan": {
                "name": "validation-plans/coverage-index.json",
                "sha256": "1" * 64,
            },
            "tiers": [],
            "policy": {},
            "attribution": {},
            "summary": {},
        }
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "index.json"
            path.write_bytes(json_bytes(report))
            with self.assertRaisesRegex(
                core.ValidationError, "identity does not match"
            ):
                coverage_index.verify_coverage_index(path, Path(directory))


if __name__ == "__main__":
    unittest.main()
