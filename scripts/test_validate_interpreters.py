#!/usr/bin/env python3

import contextlib
import io
import json
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
        "version": 1,
        "caseId": case_id,
        "backend": backend,
        "diagnostics": [],
        "outcome": {
            "success": {
                "observation": {
                    "termination": {"returned": {"value": {"nat": {"value": value}}}},
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
        "version": 1,
        "id": case_id,
        "entry": f"Fir.Validation.Source.{case_id}",
        "dependencies": [],
        "args": [{"nat": {"value": 42}}],
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
                "args": [{"nat": {"value": 7}}],
                "result": {"nat": {"value": 8}},
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
                "args": [{"nat": {"value": value}}],
                "result": {"nat": {"value": value + 1}},
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
        record["version"] = 2
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
        item["version"] = 2
        with self.assertRaisesRegex(harness.ValidationError, "protocol version 2"):
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
            self.assertEqual(artifact, {"version": 1, "cases": manifest})

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
            self.assertEqual(
                adapter.product_declarations,
                (
                    harness.ProductDeclaration(
                        "wasm-module", "modules/validation.wasm"
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

    def test_external_adapter_product_config_is_strict(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "v8.json"
            base = {
                "name": "v8",
                "buildCommand": ["node", "build.mjs"],
                "runCommand": ["node", "run.mjs"],
                "resultDomain": "selected",
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
                        "version": 1,
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

    def test_checked_native_lcnf_plan_matches_default_matrix(self) -> None:
        plan = harness.validation_plan_from_config(
            harness.ROOT / "validation-plans" / "native-lcnf.json"
        )
        self.assertEqual(plan.adapter_configs, ())
        self.assertEqual(plan.pairs, (("native", "lcnf"),))

    def test_checked_native_v8_plan_uses_real_engine_adapter(self) -> None:
        adapter_path = (
            harness.ROOT / "validation-adapters" / "v8-uint64.json"
        )
        plan = harness.validation_plan_from_config(
            harness.ROOT
            / "validation-plans"
            / "native-v8-uint64.json"
        )
        self.assertEqual(plan.adapter_configs, (adapter_path.resolve(),))
        self.assertEqual(plan.pairs, (("native", "v8"),))
        adapter = harness.external_adapter_from_config(adapter_path)
        self.assertEqual(adapter.name, "v8")
        self.assertEqual(
            adapter.build_command,
            ["lake", "lean", "FirValidationWasm.lean"],
        )
        self.assertEqual(
            adapter.run_command,
            ["node", "scripts/run_validation_v8.mjs"],
        )
        self.assertEqual(
            adapter.product_declarations,
            (
                harness.ProductDeclaration(
                    "wasm-manifest", "modules/uint64-max.wasm.json"
                ),
                harness.ProductDeclaration(
                    "wasm-module", "modules/uint64-max.wasm"
                ),
            ),
        )
        self.assertEqual(
            [(tool.kind, tool.name) for tool in adapter.tool_declarations],
            [
                ("engine", "node"),
                ("runner", "scripts/run_validation_v8.mjs"),
            ],
        )

    def test_plan_drives_external_adapter_through_cli_and_matrix(self) -> None:
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
                    {"case": success("case", self.name)},
                )

            def audit(
                self,
                context: harness.RunContext,
                backend_run: harness.BackendRun,
            ) -> harness.BackendAudit:
                return harness.BackendAudit()

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            out_dir = root / "out"
            product_path = out_dir / "v8" / "modules" / "validation.wasm"
            product_path.parent.mkdir(parents=True)
            product_bytes = b"\0asm\x01\0\0\0test-product"
            product_path.write_bytes(b"stale-product")
            adapter_path = root / "v8.json"
            runner_path = root / "runner.py"
            product_sha256 = harness.sha256_bytes(product_bytes)
            build_program = (
                "import os,pathlib;"
                "path=pathlib.Path(os.environ['FIR_VALIDATION_OUT_DIR'],"
                "'modules','validation.wasm');"
                "path.parent.mkdir(parents=True,exist_ok=True);"
                f"path.write_bytes({product_bytes!r})"
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
                            sys.executable,
                            "-c",
                            build_program,
                        ],
                        "runCommand": [engine_command, str(runner_path)],
                        "resultDomain": "selected",
                        "products": [
                            {
                                "kind": "wasm-module",
                                "path": "modules/validation.wasm",
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
                        "version": 1,
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
                    f"external/{plan_sha256}/matrix.json",
                    f"external/{adapter_sha256}/v8.json",
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
                        "kind": "engine",
                        "name": "python",
                        "sha256": engine_sha256,
                        "artifact": f"evidence/tools/{engine_sha256}",
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
            self.assertEqual(matrix["summary"]["toolCount"], 2)
            self.assertEqual(matrix["summary"]["artifactCount"], 6)
            self.assertEqual(
                [(item["kind"], item["name"]) for item in matrix["artifacts"]],
                [
                    ("backend-result", "case/native/result.json"),
                    ("backend-result", "case/v8/result.json"),
                    ("process-stderr", "v8/build/stderr.log"),
                    ("process-stderr", "v8/stderr.log"),
                    ("process-stdout", "v8/build/stdout.jsonl"),
                    ("process-stdout", "v8/stdout.jsonl"),
                ],
            )
            for item in matrix["artifacts"]:
                self.assertEqual(
                    item["artifact"], f"evidence/artifacts/{item['sha256']}"
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
            self.assertEqual(
                harness.verify_matrix_artifact(matrix_path)["identity"],
                matrix["identity"],
            )

            plan_path.unlink()
            adapter_path.unlink()
            runner_path.unlink()
            product_path.unlink()
            (out_dir / "comparisons" / "native--v8.json").unlink()
            for item in matrix["artifacts"]:
                (out_dir / item["name"]).unlink()
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
            matrix_path.write_text(
                json.dumps(valid_with_finding), encoding="utf-8"
            )
            self.assertEqual(
                harness.verify_matrix_artifact(matrix_path)["findings"],
                valid_with_finding["findings"],
            )

            evidence_bytes = evidence_path.read_bytes()
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
