#!/usr/bin/env python3
"""Compose FIR's protocol-compatible interpreter validation backends."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from validation_harness import (
    BackendAdapter,
    BackendAudit,
    BackendRun,
    BuildContext,
    ExternalCommandAdapter,
    RunContext,
    ValidationError,
    ValidationFinding,
    checked_record,
    compare_backend_results,
    compare_success,
    external_adapter_from_config,
    manifest_from_output as parse_manifest_from_output,
    records_from_output,
    result_domain_findings,
    result_map,
    run,
    select_cases,
    success_observation,
    validate_pair,
    write_comparison_artifact,
    write_corpus_manifest,
    write_process_artifacts,
)
from validation_lcnf import (
    LcnfAdapter,
    coverage_report,
    diagnostics,
    prepare_manifest as prepare_lcnf_manifest,
    write_coverage_artifact,
)


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = ROOT / "_build" / "validation"


class NativeAdapter:
    name = "native"

    def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
        return descriptors

    def build(self, context: BuildContext) -> None:
        if context.no_build:
            return
        built = run(["lake", "build", "fir-native-oracle"], context.root)
        if built.returncode != 0:
            sys.stderr.write(built.stdout + built.stderr)
            raise ValidationError("failed to build native validation backend")

    def execute(self, context: RunContext) -> BackendRun:
        backend_run = BackendRun(self.name, list(context.selected))
        for case_id in context.selected:
            command = ["lake", "exe", "fir-native-oracle", "--case", case_id]
            completed = run(command, context.root)
            write_process_artifacts(
                context.out_dir / case_id / self.name, completed
            )
            if completed.returncode != 0:
                backend_run.findings.append(
                    ValidationFinding(
                        "execution",
                        f"process exited {completed.returncode}",
                        self.name,
                        case_id,
                    )
                )
                backend_run.blocked_cases.add(case_id)
                continue
            case_results = result_map(
                records_from_output(completed.stdout, command), self.name
            )
            if set(case_results) != {case_id}:
                backend_run.findings.append(
                    ValidationFinding(
                        "execution",
                        f"backend returned {sorted(case_results)}",
                        self.name,
                        case_id,
                    )
                )
                backend_run.blocked_cases.add(case_id)
                continue
            backend_run.results[case_id] = case_results[case_id]
        return backend_run

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        return BackendAudit()


BACKEND_ADAPTERS: dict[str, BackendAdapter] = {
    "native": NativeAdapter(),
    "lcnf": LcnfAdapter(),
}


def manifest_from_output(output: str, command: list[str]) -> list[dict]:
    """Parse the current FIR corpus including its LCNF-owned extension."""
    return prepare_lcnf_manifest(parse_manifest_from_output(output, command))


def corpus_manifest() -> list[dict]:
    command = ["lake", "exe", "fir-native-oracle", "--manifest"]
    completed = run(command, ROOT)
    if completed.returncode != 0:
        raise ValidationError(f"failed to read corpus manifest:\n{completed.stderr}")
    return parse_manifest_from_output(completed.stdout, command)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="compare protocol observations from two validation backends"
    )
    parser.add_argument(
        "--case", action="append", dest="cases", help="run only this case ID"
    )
    parser.add_argument("--tag", help="run cases carrying this corpus tag")
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="reuse existing backend builds",
    )
    parser.add_argument(
        "--reference",
        default="native",
        help="backend supplying the reference observation",
    )
    parser.add_argument(
        "--candidate",
        default="lcnf",
        help="backend whose observation is checked",
    )
    parser.add_argument(
        "--adapter-config",
        action="append",
        type=Path,
        default=[],
        help="register an external protocol backend from this JSON file",
    )
    args = parser.parse_args()

    if args.reference == args.candidate:
        raise ValidationError("reference and candidate backends must differ")
    adapters = dict(BACKEND_ADAPTERS)
    for path in args.adapter_config:
        adapter = external_adapter_from_config(path)
        if adapter.name in adapters:
            raise ValidationError(
                f"backend registered more than once: {adapter.name}"
            )
        adapters[adapter.name] = adapter
    unknown_backends = sorted({args.reference, args.candidate} - adapters.keys())
    if unknown_backends:
        raise ValidationError(
            "unknown validation backend(s): "
            f"{', '.join(unknown_backends)}; registered: "
            f"{', '.join(sorted(adapters))}"
        )
    reference = adapters[args.reference]
    candidate = adapters[args.candidate]
    build_context = BuildContext(ROOT, args.out_dir, args.no_build)
    adapters_to_build = {
        adapter.name: adapter
        for adapter in (adapters["native"], reference, candidate)
    }
    for adapter in adapters_to_build.values():
        adapter.build(build_context)

    descriptors = corpus_manifest()
    for adapter in (reference, candidate):
        descriptors = adapter.prepare_manifest(descriptors)
    selected = select_cases(descriptors, args.cases, args.tag)
    write_corpus_manifest(args.out_dir, descriptors)
    context = RunContext(ROOT, args.out_dir, descriptors, selected)
    comparisons, findings = validate_pair(context, reference, candidate)
    for comparison in comparisons:
        if comparison["equal"]:
            case_id = comparison["caseId"]
            print(f"PASS {case_id:<22} {reference.name} == {candidate.name}")

    if findings:
        for finding in findings:
            print(f"FAIL {finding.render()}", file=sys.stderr)
        return 1
    print(
        f"validated {len(selected)} case(s): "
        f"{reference.name} == {candidate.name}"
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validation harness error: {error}", file=sys.stderr)
        raise SystemExit(2)
