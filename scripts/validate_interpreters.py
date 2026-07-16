#!/usr/bin/env python3
"""Compose FIR's protocol-compatible interpreter validation backends."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from validation_harness import (
    DEFAULT_OUT,
    ROOT,
    BackendAdapter,
    BackendAudit,
    BackendRun,
    BuildContext,
    ExternalCommandAdapter,
    NativeAdapter,
    RunContext,
    ValidationError,
    ValidationFinding,
    checked_record,
    compare_backend_results,
    compare_success,
    corpus_manifest,
    external_adapter_from_config,
    manifest_from_output,
    records_from_output,
    result_domain_findings,
    result_map,
    select_cases,
    success_observation,
    validate_pair,
    write_comparison_artifact,
    write_corpus_manifest,
)
from validation_lcnf import (
    LcnfAdapter,
    coverage_report,
    diagnostics,
    write_coverage_artifact,
)


BACKEND_ADAPTERS: dict[str, BackendAdapter] = {
    "native": NativeAdapter(),
    "lcnf": LcnfAdapter(),
}


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
