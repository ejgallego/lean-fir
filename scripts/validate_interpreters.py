#!/usr/bin/env python3
"""Run FIR's native oracle and final-impure LCNF candidate on one corpus."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "_build" / "validation"
PROTOCOL_VERSION = 1


class ValidationError(RuntimeError):
    pass


def run(command: list[str], timeout: int = 120) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            cwd=ROOT,
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


def diagnostics(record: dict) -> dict[str, str]:
    result: dict[str, str] = {}
    for item in record.get("diagnostics", []):
        if isinstance(item, dict) and isinstance(item.get("key"), str):
            result[item["key"]] = str(item.get("value", ""))
    return result


def success_observation(record: dict) -> dict:
    case_id, outcome = checked_record(record, str(record["backend"]))
    success = outcome.get("success")
    if not isinstance(success, dict) or not isinstance(success.get("observation"), dict):
        status = next(iter(outcome))
        raise ValidationError(f"{record['backend']}/{case_id}: backend status is {status}")
    return success["observation"]


def compare_success(native: dict, candidate: dict) -> tuple[bool, dict, dict]:
    native_observation = success_observation(native)
    candidate_observation = success_observation(candidate)
    return native_observation == candidate_observation, native_observation, candidate_observation


def write_artifact(out_dir: Path, case_id: str, backend: str, record: dict) -> None:
    destination = out_dir / case_id / backend
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "result.json").write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="compare Lean native execution with FIR's final-impure interpreter"
    )
    parser.add_argument("--case", action="append", dest="cases", help="run only this case ID")
    parser.add_argument("--tag", help="run cases carrying this corpus tag")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--no-build", action="store_true", help="reuse the existing native executable")
    args = parser.parse_args()

    if not args.no_build:
        built = run(["lake", "build", "fir-native-oracle"])
        if built.returncode != 0:
            sys.stderr.write(built.stdout + built.stderr)
            raise ValidationError("failed to build fir-native-oracle")

    list_command = ["lake", "exe", "fir-native-oracle", "--list"]
    listed = run(list_command)
    if listed.returncode != 0:
        raise ValidationError(f"failed to list corpus cases:\n{listed.stderr}")
    all_cases = [line.strip() for line in listed.stdout.splitlines() if line.strip()]
    if len(set(all_cases)) != len(all_cases):
        raise ValidationError("native corpus contains duplicate case IDs")
    tagged_cases = all_cases
    if args.tag:
        tagged = run(list_command + ["--tag", args.tag])
        if tagged.returncode != 0:
            raise ValidationError(f"failed to select corpus tag {args.tag}:\n{tagged.stderr}")
        tagged_cases = [line.strip() for line in tagged.stdout.splitlines() if line.strip()]
        if not tagged_cases:
            raise ValidationError(f"corpus tag selected no cases: {args.tag}")
    selected = args.cases or tagged_cases
    unknown = sorted(set(selected) - set(all_cases))
    if unknown:
        raise ValidationError(f"unknown validation case(s): {', '.join(unknown)}")

    lcnf_command = ["lake", "env", "lean", "FirValidationLCNF.lean"]
    lcnf_run = run(lcnf_command)
    (args.out_dir / "lcnf").mkdir(parents=True, exist_ok=True)
    (args.out_dir / "lcnf" / "stdout.jsonl").write_text(lcnf_run.stdout, encoding="utf-8")
    (args.out_dir / "lcnf" / "stderr.log").write_text(lcnf_run.stderr, encoding="utf-8")
    if lcnf_run.returncode != 0:
        raise ValidationError(f"LCNF backend failed:\n{lcnf_run.stdout}{lcnf_run.stderr}")
    lcnf_results = result_map(records_from_output(lcnf_run.stdout, lcnf_command), "lcnf")

    failures: list[str] = []
    comparisons: list[dict] = []
    for case_id in selected:
        native_command = ["lake", "exe", "fir-native-oracle", "--case", case_id]
        native_run = run(native_command)
        if native_run.returncode != 0:
            failures.append(f"{case_id}: native process exited {native_run.returncode}")
            continue
        native_records = records_from_output(native_run.stdout, native_command)
        native_results = result_map(native_records, "native")
        if set(native_results) != {case_id}:
            failures.append(f"{case_id}: native backend returned {sorted(native_results)}")
            continue
        native = native_results[case_id]
        candidate = lcnf_results.get(case_id)
        if candidate is None:
            failures.append(f"{case_id}: LCNF backend returned no result")
            continue
        write_artifact(args.out_dir, case_id, "native", native)
        write_artifact(args.out_dir, case_id, "lcnf", candidate)
        native_dir = args.out_dir / case_id / "native"
        (native_dir / "stdout.jsonl").write_text(native_run.stdout, encoding="utf-8")
        (native_dir / "stderr.log").write_text(native_run.stderr, encoding="utf-8")
        missing_forms = diagnostics(candidate).get("missing-lcnf-forms", "")
        if missing_forms:
            failures.append(f"{case_id}: missing required LCNF forms: {missing_forms}")
            continue
        try:
            equal, native_observation, lcnf_observation = compare_success(native, candidate)
        except ValidationError as error:
            failures.append(str(error))
            continue
        if not equal:
            failures.append(
                f"{case_id}: semantic mismatch\n"
                f"  native={json.dumps(native_observation, sort_keys=True)}\n"
                f"  lcnf={json.dumps(lcnf_observation, sort_keys=True)}"
            )
            continue
        comparisons.append(
            {"caseId": case_id, "oracle": "native", "candidate": "lcnf", "equal": True}
        )
        forms = diagnostics(candidate).get("lcnf-forms", "-")
        print(f"PASS {case_id:<22} lcnf=[{forms}]")

    extra_lcnf = sorted(set(lcnf_results) - set(all_cases))
    missing_lcnf = sorted(set(all_cases) - set(lcnf_results))
    if extra_lcnf:
        failures.append(f"LCNF backend returned unknown cases: {', '.join(extra_lcnf)}")
    if missing_lcnf:
        failures.append(f"LCNF backend omitted cases: {', '.join(missing_lcnf)}")

    if failures:
        for failure in failures:
            print(f"FAIL {failure}", file=sys.stderr)
        return 1
    args.out_dir.mkdir(parents=True, exist_ok=True)
    (args.out_dir / "comparison.json").write_text(
        json.dumps({"version": PROTOCOL_VERSION, "comparisons": comparisons}, indent=2)
        + "\n",
        encoding="utf-8",
    )
    print(f"validated {len(selected)} case(s): native == final-impure LCNF")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validation harness error: {error}", file=sys.stderr)
        raise SystemExit(2)
