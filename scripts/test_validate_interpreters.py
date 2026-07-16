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
    case_id: str, *, tags: list[str] | None = None, forms: list[str] | None = None
) -> dict:
    return {
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
    }


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
        second = descriptor("z-case", tags=["slow", "quick"], forms=["return", "inc"])
        first = descriptor("a-case")
        output = "compiler noise\n" + json.dumps(second) + "\n" + json.dumps(first) + "\n"
        manifest = harness.manifest_from_output(output, ["native", "--manifest"])
        self.assertEqual([item["id"] for item in manifest], ["a-case", "z-case"])
        self.assertEqual(manifest[1]["tags"], ["quick", "slow"])
        self.assertEqual(manifest[1]["requiredLcnfForms"], ["inc", "return"])

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


if __name__ == "__main__":
    unittest.main()
