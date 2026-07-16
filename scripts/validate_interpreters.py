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
    PairValidationResult,
    ProductDeclaration,
    RunContext,
    ToolDeclaration,
    ValidationError,
    ValidationFinding,
    ValidationInput,
    ValidationPlan,
    ValidationProduct,
    ValidationTool,
    canonical_json_sha256,
    checked_record,
    comparison_artifact_path,
    compare_backend_results,
    compare_success,
    corpus_artifact_bytes,
    external_adapter_from_config,
    manifest_from_output as parse_manifest_from_output,
    product_receipt_findings,
    product_receipt_value,
    records_from_output,
    retain_evidence_blob,
    result_domain_findings,
    result_map,
    resolve_lake_command,
    run,
    select_cases,
    sha256_bytes,
    success_observation,
    validate_pair,
    validate_backend_name,
    validate_matrix,
    verify_matrix_artifact,
    validation_plan_from_config,
    validation_run_sha256,
    validation_selection_sha256,
    validation_input_from_file,
    validation_product_from_file,
    validation_tool_from_file,
    validation_tool_from_declaration,
    write_comparison_artifact,
    write_corpus_manifest,
    write_matrix_artifact,
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

    def __init__(self) -> None:
        self.root: Path | None = None
        self.executable: Path | None = None
        self.tool: ValidationTool | None = None

    def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
        return descriptors

    def build(self, context: BuildContext) -> None:
        self.root = None
        self.executable = None
        self.tool = None
        if context.no_build:
            pass
        else:
            built = run(["lake", "build", "fir-native-oracle"], context.root)
            if built.returncode != 0:
                sys.stderr.write(built.stdout + built.stderr)
                raise ValidationError("failed to build native validation backend")
        self.executable = resolve_lake_command(
            context.root, "fir-native-oracle"
        )
        self.root = context.root
        self.tool = validation_tool_from_file(
            self.name,
            "executable",
            ".lake/build/bin/fir-native-oracle",
            self.executable,
        )

    def verify_tool(self) -> None:
        if self.executable is None or self.tool is None:
            raise ValidationError("native adapter must be built before execution")
        current = validation_tool_from_file(
            self.name,
            self.tool.kind,
            self.tool.name,
            self.executable,
        )
        if current != self.tool:
            raise ValidationError("native validation executable changed during run")

    def manifest(self) -> list[dict]:
        self.verify_tool()
        if self.executable is None or self.root is None:
            raise ValidationError("native adapter must be built before execution")
        command = [str(self.executable), "--manifest"]
        completed = run(command, self.root)
        self.verify_tool()
        if completed.returncode != 0:
            raise ValidationError(
                f"failed to read corpus manifest:\n{completed.stderr}"
            )
        return parse_manifest_from_output(completed.stdout, command)

    def execute(self, context: RunContext) -> BackendRun:
        self.verify_tool()
        if self.executable is None or self.tool is None:
            raise ValidationError("native adapter must be built before execution")
        backend_run = BackendRun(
            self.name,
            list(context.selected),
            tools=[self.tool],
        )
        for case_id in context.selected:
            command = [str(self.executable), "--case", case_id]
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
        self.verify_tool()
        return backend_run

    def audit(self, context: RunContext, backend_run: BackendRun) -> BackendAudit:
        return BackendAudit()


NATIVE_ADAPTER = NativeAdapter()


BACKEND_ADAPTERS: dict[str, BackendAdapter] = {
    "native": NATIVE_ADAPTER,
    "lcnf": LcnfAdapter(),
}


def manifest_from_output(output: str, command: list[str]) -> list[dict]:
    """Parse the current FIR corpus including its LCNF-owned extension."""
    return prepare_lcnf_manifest(parse_manifest_from_output(output, command))


def corpus_manifest() -> list[dict]:
    return NATIVE_ADAPTER.manifest()


def parse_pair_spec(specification: str) -> tuple[str, str]:
    parts = specification.split(":")
    if len(parts) != 2:
        raise ValidationError(
            f"comparison pair must be REFERENCE:CANDIDATE: {specification}"
        )
    reference = validate_backend_name(parts[0], "reference backend")
    candidate = validate_backend_name(parts[1], "candidate backend")
    if reference == candidate:
        raise ValidationError(
            f"comparison pair must use distinct backends: {reference}"
        )
    return reference, candidate


def main() -> int:
    parser = argparse.ArgumentParser(
        description="compare protocol observations from two validation backends"
    )
    parser.add_argument(
        "--case", action="append", dest="cases", help="run only this case ID"
    )
    parser.add_argument("--tag", help="run cases carrying this corpus tag")
    parser.add_argument("--out-dir", type=Path)
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="reuse existing backend builds",
    )
    parser.add_argument(
        "--reference",
        default=None,
        help="single-pair reference when --pair is absent",
    )
    parser.add_argument(
        "--candidate",
        default=None,
        help="single-pair candidate when --pair is absent",
    )
    parser.add_argument(
        "--pair",
        action="append",
        default=[],
        metavar="REFERENCE:CANDIDATE",
        help="add a directed comparison pair; may be repeated",
    )
    parser.add_argument(
        "--adapter-config",
        action="append",
        type=Path,
        default=[],
        help="register an external protocol backend from this JSON file",
    )
    parser.add_argument(
        "--plan",
        type=Path,
        help="load adapter configs and directed pairs from this JSON plan",
    )
    parser.add_argument(
        "--verify-matrix",
        type=Path,
        help="verify retained evidence and identities without running backends",
    )
    args = parser.parse_args()

    if args.verify_matrix is not None:
        if (
            args.cases
            or args.tag
            or args.out_dir is not None
            or args.no_build
            or args.reference
            or args.candidate
            or args.pair
            or args.adapter_config
            or args.plan
        ):
            raise ValidationError(
                "--verify-matrix cannot be combined with validation run options"
            )
        matrix = verify_matrix_artifact(args.verify_matrix)
        print(
            f"verified validation matrix {args.verify_matrix}: "
            f"run {matrix['identity']['run']}"
        )
        return 0

    args.out_dir = args.out_dir or DEFAULT_OUT

    provenance_inputs = []
    if args.plan is not None:
        if args.pair or args.adapter_config or args.reference or args.candidate:
            raise ValidationError(
                "--plan cannot be combined with --pair, --adapter-config, "
                "--reference, or --candidate"
            )
        plan_input = validation_input_from_file(
            "validation-plan", args.plan, ROOT
        )
        provenance_inputs.append(plan_input)
        plan = validation_plan_from_config(args.plan, plan_input.content)
        pair_names = list(plan.pairs)
        adapter_config_paths = list(plan.adapter_configs)
    else:
        pair_names = (
            [parse_pair_spec(specification) for specification in args.pair]
            if args.pair
            else [
                parse_pair_spec(
                    f"{args.reference or 'native'}:{args.candidate or 'lcnf'}"
                )
            ]
        )
        adapter_config_paths = args.adapter_config
    if len(set(pair_names)) != len(pair_names):
        raise ValidationError("comparison pair selected more than once")
    adapter_inputs = [
        validation_input_from_file("adapter-config", path, ROOT)
        for path in adapter_config_paths
    ]
    provenance_inputs.extend(adapter_inputs)
    adapters = dict(BACKEND_ADAPTERS)
    for path, adapter_input in zip(adapter_config_paths, adapter_inputs):
        adapter = external_adapter_from_config(path, adapter_input.content)
        if adapter.name in adapters:
            raise ValidationError(
                f"backend registered more than once: {adapter.name}"
            )
        adapters[adapter.name] = adapter
    requested_backends = {
        backend for pair_name in pair_names for backend in pair_name
    }
    unknown_backends = sorted(requested_backends - adapters.keys())
    if unknown_backends:
        raise ValidationError(
            "unknown validation backend(s): "
            f"{', '.join(unknown_backends)}; registered: "
            f"{', '.join(sorted(adapters))}"
        )
    pairs = [
        (adapters[reference], adapters[candidate])
        for reference, candidate in pair_names
    ]
    participating_adapters = {
        adapter.name: adapter for pair in pairs for adapter in pair
    }
    build_context = BuildContext(ROOT, args.out_dir, args.no_build)
    adapters_to_build = {
        adapter.name: adapter
        for adapter in (adapters["native"], *participating_adapters.values())
    }
    for adapter in adapters_to_build.values():
        adapter.build(build_context)

    descriptors = corpus_manifest()
    for adapter in participating_adapters.values():
        descriptors = adapter.prepare_manifest(descriptors)
    selected = select_cases(descriptors, args.cases, args.tag)
    write_corpus_manifest(args.out_dir, descriptors)
    context = RunContext(
        ROOT,
        args.out_dir,
        descriptors,
        selected,
        tuple(provenance_inputs),
    )
    pair_results, findings = validate_matrix(context, pairs)
    for pair_result in pair_results:
        for comparison in pair_result.comparisons:
            if comparison["equal"]:
                case_id = comparison["caseId"]
                print(
                    f"PASS {case_id:<22} "
                    f"{pair_result.reference} == {pair_result.candidate}"
                )

    if findings:
        for finding in findings:
            print(f"FAIL {finding.render()}", file=sys.stderr)
        return 1
    print(
        f"validated {len(selected)} case(s) across {len(pair_results)} pair(s): "
        + ", ".join(
            f"{result.reference} == {result.candidate}"
            for result in pair_results
        )
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValidationError as error:
        print(f"validation harness error: {error}", file=sys.stderr)
        raise SystemExit(2)
