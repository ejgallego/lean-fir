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
import validation_harness as core
import validation_lcnf as lcnf


def success(case_id: str, backend: str, value: int = 42) -> dict:
    return {
        "version": 2,
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
        "version": 2,
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
    externals: list[str] | None = None,
    executed_externals: list[str] | None = None,
    effect_projections: list[dict] | None = None,
) -> dict:
    item = {
        "version": 2,
        "id": case_id,
        "entry": f"Fir.Validation.Source.{case_id}",
        "dependencies": [],
        "args": [{"nat": {"value": "42"}}],
        "argSchemas": ["nat"],
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
        "requiredExternals": externals or [],
        "requiredExecutedExternals": executed_externals or [],
        "effectProjections": effect_projections or [],
    }
    return item


def with_form_diagnostics(
    record: dict,
    *,
    static: str | None = None,
    executed: str | None = None,
    steps: str | None = "1",
    static_externals: str | None = "",
    missing_static_externals: str | None = "",
    executed_externals: str | None = "",
    missing_executed_externals: str | None = "",
) -> dict:
    diagnostics = []
    if static is not None:
        diagnostics.append({"key": "lcnf-forms", "value": static})
    if executed is not None:
        diagnostics.append({"key": "executed-lcnf-forms", "value": executed})
    if steps is not None:
        diagnostics.append({"key": "interpreter-steps", "value": steps})
    if static_externals is not None:
        diagnostics.append({"key": "externals", "value": static_externals})
    if missing_static_externals is not None:
        diagnostics.append(
            {"key": "missing-externals", "value": missing_static_externals}
        )
    if executed_externals is not None:
        diagnostics.append({"key": "executed-externals", "value": executed_externals})
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
            harness.ValidationError, "missing requiredExecutedExternals"
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
        record["version"] = 3
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
            externals=["Nat.add", "ByteArray.size"],
            executed_externals=["Nat.add", "ByteArray.size"],
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
            manifest[1]["requiredExternals"], ["ByteArray.size", "Nat.add"]
        )
        self.assertEqual(
            manifest[1]["requiredExecutedExternals"], ["ByteArray.size", "Nat.add"]
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
        item["version"] = 3
        with self.assertRaisesRegex(harness.ValidationError, "protocol version 3"):
            harness.manifest_from_output(json.dumps(item), ["native", "--manifest"])

    def test_manifest_argument_arity_rejected(self) -> None:
        item = descriptor("case")
        item["argSchemas"] = []
        with self.assertRaisesRegex(harness.ValidationError, "argument arity mismatch"):
            harness.manifest_from_output(json.dumps(item), ["native", "--manifest"])

    def test_manifest_drives_tag_and_explicit_selection(self) -> None:
        manifest = [
            descriptor("a-case", tags=["quick"]),
            descriptor("b-case", tags=["extended"]),
        ]
        self.assertEqual(harness.select_cases(manifest, None, "quick"), ["a-case"])
        self.assertEqual(harness.select_cases(manifest, ["b-case"], "quick"), ["b-case"])
        with self.assertRaisesRegex(harness.ValidationError, "selected no cases"):
            harness.select_cases(manifest, None, "missing")

    def test_corpus_artifact_is_deterministic(self) -> None:
        manifest = [descriptor("a-case", tags=["quick", "data"])]
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            harness.write_corpus_manifest(out_dir, manifest)
            first = (out_dir / "corpus.json").read_bytes()
            harness.write_corpus_manifest(out_dir, manifest)
            self.assertEqual(first, (out_dir / "corpus.json").read_bytes())
            artifact = json.loads(first)
            self.assertEqual(artifact, {"version": 2, "cases": manifest})

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
                    "version": 2,
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
                "version": 2,
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
                    {"version": 2, "products": []},
                    "nonempty array",
                ),
                (
                    {"version": 2, "products": [], "extra": True},
                    "must contain version and products",
                ),
                (
                    {
                        "version": 2,
                        "products": [
                            {"kind": "wasm-module", "path": "module.wasm"},
                            {"kind": "debug-info", "path": "module.wasm"},
                        ],
                    },
                    "duplicate product path",
                ),
                (
                    {
                        "version": 2,
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
                            "version": 2,
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
                        "version": 2,
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
                {"version": 2, "scope": "exact", "inputs": [valid]},
                {"version": 2, "scope": "reported-loaded", "inputs": []},
                {
                    "version": 2,
                    "scope": "reported-loaded",
                    "inputs": [valid, valid],
                },
                {
                    "version": 2,
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
                    "version": 2,
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
                "version": 2,
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
                    "version": 2,
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
                        "version": 2,
                        "adapterConfigs": [
                            "../adapters/v8.json",
                            "../adapters/talos.json",
                        ],
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
                "manifest={'version':2,'contract':contract,'products':["
                "{'kind':'wasm-module','path':'module.wasm'}],'cases':["
                "{'caseId':'case','products':[{'kind':'wasm-module',"
                "'path':'module.wasm'}]}]};"
                "(root/'bundle.json').write_text(json.dumps(manifest))"
            )
            provider_path = root / "provider.json"
            provider_value = {
                "version": 2,
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
                "import json,os;"
                "backend=os.environ['FIR_VALIDATION_BACKEND'];"
                "bundle=json.loads(os.environ['FIR_VALIDATION_PRODUCT_BUNDLE']);"
                "products=json.loads(os.environ['FIR_VALIDATION_PRODUCTS']);"
                "assert len(products)==1 and products[0]['backend']=='fixture-wasm';"
                "binding=bundle['cases'][0]['products'];"
                "receipt={'provider':bundle['provider'],"
                "'bundleSha256':bundle['bundleSha256'],'products':["
                "{'kind':item['kind'],'name':item['name'],'sha256':item['sha256']}"
                " for item in binding]};"
                "record={'version':2,'caseId':'case','backend':backend,"
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
                        "version": 2,
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
                    "version": 2,
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
                        "version": 2,
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
                    "version": 2,
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
                "closure={'version':2,'scope':'reported-loaded','inputs':["
                "{'kind':'fixture-source','name':'compiler.input','path':"
                f"{str(material_path)!r}" "}]};"
                "pathlib.Path(os.environ['FIR_VALIDATION_OUT_DIR'],"
                "'build-inputs.json').write_text(json.dumps(closure))"
            )
            program = (
                "import hashlib,json,os,pathlib;"
                "products=json.loads(os.environ['FIR_VALIDATION_PRODUCTS']);"
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
                        "version": 2,
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
            self.assertEqual(matrix["summary"]["artifactCount"], 18)
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
            same_comparison = core.compare_verified_evidence(
                core.verify_evidence_snapshot(evidence_path),
                core.verify_evidence_snapshot(moved_evidence),
            )
            self.assertFalse(any(same_comparison["classification"].values()))
            self.assertEqual(same_comparison["semanticResults"], [])
            self.assertIn(
                "contract same",
                "\n".join(core.render_evidence_comparison(same_comparison)),
            )

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
                "import json,os;"
                "assert json.loads(os.environ['FIR_VALIDATION_CASES']) == ['case'];"
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
                ["v8/stdout.jsonl", "v8/stderr.log"],
            )
            self.assertTrue((out_dir / "v8" / "stdout.jsonl").is_file())

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
            ["case: missing executed-lcnf-forms diagnostic"],
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


if __name__ == "__main__":
    unittest.main()
