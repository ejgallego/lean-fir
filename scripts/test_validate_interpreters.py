#!/usr/bin/env python3

import json
import tempfile
import unittest
from pathlib import Path

import validate_interpreters as harness


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


def descriptor(
    case_id: str,
    *,
    tags: list[str] | None = None,
    forms: list[str] | None = None,
    executed_forms: list[str] | None = None,
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
    }
    return item


def with_form_diagnostics(
    record: dict,
    *,
    static: str | None = None,
    executed: str | None = None,
    steps: str | None = "1",
) -> dict:
    diagnostics = []
    if static is not None:
        diagnostics.append({"key": "lcnf-forms", "value": static})
    if executed is not None:
        diagnostics.append({"key": "executed-lcnf-forms", "value": executed})
    if steps is not None:
        diagnostics.append({"key": "interpreter-steps", "value": steps})
    record["diagnostics"] = diagnostics
    return record


class HarnessTests(unittest.TestCase):
    def test_equal_successes(self) -> None:
        equal, _, _ = harness.compare_success(success("case", "native"), success("case", "lcnf"))
        self.assertTrue(equal)

    def test_semantic_mismatch(self) -> None:
        equal, _, _ = harness.compare_success(
            success("case", "native", 41), success("case", "lcnf", 42)
        )
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
            failures, ["case: missing required static LCNF forms: inc"]
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
        self.assertEqual(failures, ["case: missing executed-lcnf-forms diagnostic"])
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
        self.assertEqual(failures, ["case: missing interpreter-steps diagnostic"])

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
                    failures,
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
            failures, ["case: missing required executed LCNF forms: cases"]
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
