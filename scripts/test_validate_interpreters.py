#!/usr/bin/env python3

import json
import sys
import tempfile
import unittest
from pathlib import Path

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
        self.assertIs(harness.LcnfAdapter, lcnf.LcnfAdapter)
        self.assertIs(harness.coverage_report, lcnf.coverage_report)

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
            first = (out_dir / "comparison.json").read_bytes()
            harness.write_comparison_artifact(
                out_dir, "native", "v8", comparisons
            )
            self.assertEqual(first, (out_dir / "comparison.json").read_bytes())
            artifact = json.loads(first)
            self.assertEqual(artifact["reference"], "native")
            self.assertEqual(artifact["candidate"], "v8")
            self.assertEqual(artifact["comparisons"], comparisons)

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
                (Path(directory) / "comparison.json").read_text(encoding="utf-8")
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

    def test_external_adapter_config_uses_argv_not_a_shell_command(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "v8.json"
            path.write_text(
                json.dumps(
                    {
                        "name": "v8",
                        "buildCommand": ["node", "scripts/build-v8.mjs"],
                        "runCommand": ["node", "scripts/run-v8.mjs"],
                        "resultDomain": "selected",
                        "timeoutSeconds": 30,
                    }
                ),
                encoding="utf-8",
            )
            adapter = harness.external_adapter_from_config(path)
            self.assertEqual(adapter.name, "v8")
            self.assertEqual(adapter.run_command, ["node", "scripts/run-v8.mjs"])
            self.assertEqual(adapter.result_domain, "selected")
            self.assertEqual(adapter.timeout_seconds, 30)

            value = json.loads(path.read_text(encoding="utf-8"))
            value["runCommand"] = "node scripts/run-v8.mjs"
            path.write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaisesRegex(harness.ValidationError, "argv array"):
                harness.external_adapter_from_config(path)

    def test_external_adapter_receives_corpus_and_selection_environment(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            out_dir = Path(directory)
            descriptors = [descriptor("case")]
            harness.write_corpus_manifest(out_dir, descriptors)
            record = success("case", "v8")
            program = (
                "import json,os;"
                "assert json.loads(os.environ['FIR_VALIDATION_CASES']) == ['case'];"
                "assert os.path.isfile(os.environ['FIR_VALIDATION_CORPUS']);"
                "assert os.environ['FIR_VALIDATION_BACKEND'] == 'v8';"
                f"print({json.dumps(json.dumps(record))})"
            )
            adapter = harness.ExternalCommandAdapter(
                "v8", [sys.executable, "-c", program], "selected"
            )
            context = harness.RunContext(
                harness.ROOT, out_dir, descriptors, ["case"]
            )
            backend_run = adapter.execute(context)
            self.assertEqual(backend_run.findings, [])
            self.assertEqual(backend_run.expected_cases, ["case"])
            self.assertEqual(backend_run.results, {"case": record})
            self.assertTrue((out_dir / "v8" / "stdout.jsonl").is_file())

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
