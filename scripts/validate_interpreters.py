#!/usr/bin/env python3
"""Compose FIR's protocol-compatible interpreter validation backends."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from validation_harness import (
    BackendAdapter,
    BackendAudit,
    BackendRun,
    BuildInputDeclaration,
    BuildContext,
    ExternalCommandAdapter,
    PairValidationResult,
    ProductBundle,
    ProductConsumer,
    ProductContract,
    ProductDeclaration,
    ProductProviderRequirement,
    ProductProviderRun,
    ProductReceipt,
    RunContext,
    ToolDeclaration,
    ValidationArtifact,
    ValidationBuildInput,
    ValidationError,
    ValidationFinding,
    ValidationInput,
    ValidationPlan,
    ValidationProduct,
    ValidationTool,
    canonical_json_sha256,
    build_product_providers,
    checked_record,
    comparison_artifact_path,
    compare_backend_results,
    compare_verified_evidence,
    compare_success,
    corpus_artifact_bytes,
    external_adapter_from_config,
    external_product_provider_from_config,
    manifest_from_output as parse_manifest_from_output,
    product_receipt_findings,
    product_receipt_value,
    product_bundle_receipt_findings,
    product_bundle_receipt_value,
    records_from_output,
    render_evidence_comparison,
    render_validation_coverage,
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
    validation_evidence_manifest_path,
    validation_evidence_sha256,
    verify_matrix_artifact,
    verify_evidence_manifest,
    verify_evidence_snapshot,
    validation_plan_from_config,
    validation_run_sha256,
    validation_selection_sha256,
    validation_input_from_file,
    validation_artifact_scope,
    validation_build_input_from_file,
    validation_product_from_file,
    validation_tool_from_file,
    validation_tool_from_declaration,
    write_comparison_artifact,
    write_corpus_manifest,
    write_evidence_manifest,
    write_artifact,
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
from validation_direct_lcnf import (
    DIRECT_LCNF_ADAPTER,
    DIRECT_NATIVE_ADAPTER,
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
            backend_run.artifacts.extend(
                write_process_artifacts(
                    context.out_dir / case_id / self.name,
                    completed,
                    f"{case_id}/{self.name}",
                )
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
    "direct-native": DIRECT_NATIVE_ADAPTER,
    "direct-lcnf": DIRECT_LCNF_ADAPTER,
}


def manifest_from_output(output: str, command: list[str]) -> list[dict]:
    """Parse the current FIR corpus including its LCNF-owned extension."""
    return prepare_lcnf_manifest(parse_manifest_from_output(output, command))


def corpus_manifest(adapter: BackendAdapter = NATIVE_ADAPTER) -> list[dict]:
    manifest = getattr(adapter, "manifest", None)
    if not callable(manifest):
        raise ValidationError(
            f"validation corpus backend {adapter.name} does not provide a manifest"
        )
    return manifest()


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
        "--corpus-backend",
        help="manifest-owning backend; defaults to native",
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
        "--provider-config",
        action="append",
        type=Path,
        default=[],
        help="register a shared product provider from this JSON file",
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
    parser.add_argument(
        "--verify-evidence",
        type=Path,
        help="verify an immutable evidence manifest without running backends",
    )
    parser.add_argument(
        "--compare-evidence",
        nargs=2,
        type=Path,
        metavar=("BEFORE", "AFTER"),
        help="verify and compare two immutable evidence manifests",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit --compare-evidence as stable JSON",
    )
    args = parser.parse_args()

    evidence_modes = sum(
        int(option is not None)
        for option in (
            args.verify_matrix,
            args.verify_evidence,
            args.compare_evidence,
        )
    )
    if evidence_modes:
        if (
            evidence_modes != 1
            or args.cases
            or args.tag
            or args.out_dir is not None
            or args.no_build
            or args.reference
            or args.candidate
            or args.corpus_backend
            or args.pair
            or args.adapter_config
            or args.provider_config
            or args.plan
            or (args.json and args.compare_evidence is None)
        ):
            raise ValidationError(
                "evidence inspection options are mutually exclusive and "
                "cannot be combined with validation run options"
            )
        if args.compare_evidence is not None:
            before_path, after_path = args.compare_evidence
            comparison = compare_verified_evidence(
                verify_evidence_snapshot(before_path),
                verify_evidence_snapshot(after_path),
            )
            if args.json:
                print(json.dumps(comparison, indent=2, sort_keys=True))
            else:
                for line in render_evidence_comparison(comparison):
                    print(line)
        elif args.verify_matrix is not None:
            matrix = verify_matrix_artifact(args.verify_matrix)
            print(
                f"verified validation matrix {args.verify_matrix}: "
                f"run {matrix['identity']['run']}"
            )
            for line in render_validation_coverage(matrix["coverage"]):
                print(line)
        else:
            evidence_path = args.verify_evidence
            if evidence_path is None:
                raise ValidationError("missing validation evidence path")
            manifest = verify_evidence_manifest(evidence_path)
            print(
                f"verified validation evidence {evidence_path}: "
                f"evidence {manifest['identity']['evidence']}, "
                f"run {manifest['identity']['run']}"
            )
            for line in render_validation_coverage(manifest["coverage"]):
                print(line)
        return 0

    if args.json:
        raise ValidationError("--json requires --compare-evidence")

    args.out_dir = args.out_dir or DEFAULT_OUT

    provenance_inputs = []
    if args.plan is not None:
        if (
            args.pair
            or args.adapter_config
            or args.provider_config
            or args.reference
            or args.candidate
            or args.corpus_backend
        ):
            raise ValidationError(
                "--plan cannot be combined with --pair, --adapter-config, "
                "--provider-config, --reference, --candidate, or "
                "--corpus-backend"
            )
        plan_input = validation_input_from_file(
            "validation-plan", args.plan, ROOT
        )
        provenance_inputs.append(plan_input)
        plan = validation_plan_from_config(args.plan, plan_input.content)
        pair_names = list(plan.pairs)
        corpus_backend_name = plan.corpus_backend
        adapter_config_paths = list(plan.adapter_configs)
        provider_config_paths = list(plan.provider_configs)
    else:
        corpus_backend_name = args.corpus_backend or "native"
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
        provider_config_paths = args.provider_config
    if len(set(pair_names)) != len(pair_names):
        raise ValidationError("comparison pair selected more than once")
    provider_inputs = [
        validation_input_from_file("provider-config", path, ROOT)
        for path in provider_config_paths
    ]
    provenance_inputs.extend(provider_inputs)
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
    providers = {}
    for path, provider_input in zip(provider_config_paths, provider_inputs):
        provider = external_product_provider_from_config(
            path, provider_input.content
        )
        if provider.name in providers:
            raise ValidationError(
                f"product provider registered more than once: {provider.name}"
            )
        if provider.name in adapters:
            raise ValidationError(
                f"product provider and backend names overlap: {provider.name}"
            )
        providers[provider.name] = provider
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
    if corpus_backend_name not in adapters:
        raise ValidationError(
            f"unknown validation corpus backend: {corpus_backend_name}; "
            f"registered: {', '.join(sorted(adapters))}"
        )
    pairs = [
        (adapters[reference], adapters[candidate])
        for reference, candidate in pair_names
    ]
    participating_adapters = {
        adapter.name: adapter for pair in pairs for adapter in pair
    }
    required_provider_names = {
        requirement.provider
        for adapter in participating_adapters.values()
        for requirement in [getattr(adapter, "product_provider", None)]
        if isinstance(requirement, ProductProviderRequirement)
    }
    unknown_providers = sorted(required_provider_names - providers.keys())
    if unknown_providers:
        raise ValidationError(
            "unknown product provider(s): " + ", ".join(unknown_providers)
        )
    unused_providers = sorted(providers.keys() - required_provider_names)
    if unused_providers:
        raise ValidationError(
            "unused product provider(s): " + ", ".join(unused_providers)
        )
    corpus_adapter = adapters[corpus_backend_name]
    corpus_adapter.build(
        BuildContext(ROOT, args.out_dir, args.no_build)
    )
    descriptors = corpus_manifest(corpus_adapter)
    for adapter in participating_adapters.values():
        descriptors = adapter.prepare_manifest(descriptors)
    selected = select_cases(descriptors, args.cases, args.tag)
    write_corpus_manifest(args.out_dir, descriptors)
    base_context = RunContext(
        ROOT,
        args.out_dir,
        descriptors,
        selected,
        tuple(provenance_inputs),
    )
    provider_build_context = BuildContext(
        ROOT, args.out_dir, args.no_build, run_context=base_context
    )
    provider_runs = build_product_providers(
        provider_build_context,
        tuple(providers[name] for name in sorted(required_provider_names)),
    )
    context = RunContext(
        ROOT,
        args.out_dir,
        descriptors,
        selected,
        tuple(provenance_inputs),
        {run.provider: run.bundle for run in provider_runs},
    )
    build_context = BuildContext(
        ROOT, args.out_dir, args.no_build, run_context=context
    )
    adapters_to_build = {
        adapter.name: adapter
        for adapter in participating_adapters.values()
        if adapter.name != corpus_backend_name
    }
    for adapter in adapters_to_build.values():
        adapter.build(build_context)
    pair_results, findings = validate_matrix(
        context, pairs, provider_runs
    )
    matrix_content = (args.out_dir / "matrix.json").read_bytes()
    matrix = json.loads(matrix_content)
    evidence_path = validation_evidence_manifest_path(
        args.out_dir,
        matrix["identity"]["run"],
        sha256_bytes(matrix_content),
    )
    verify_evidence_manifest(evidence_path)
    print(f"retained validation evidence {evidence_path}")
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
        for line in render_validation_coverage(matrix["coverage"]):
            print(line)
        return 1
    for line in render_validation_coverage(matrix["coverage"]):
        print(line)
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
