#!/usr/bin/env python3
"""Protocol adapters for validation-owned direct final-impure LCNF cases."""

from __future__ import annotations

import sys
from pathlib import Path

from validation_harness import (
    BackendAudit,
    BackendRun,
    BuildContext,
    RunContext,
    ValidationError,
    ValidationFinding,
    ValidationTool,
    manifest_from_output,
    records_from_output,
    resolve_lake_command,
    result_map,
    run,
    validation_tool_from_file,
    write_process_artifacts,
)
from validation_lcnf import (
    coverage_report,
    prepare_manifest,
    write_coverage_artifact,
)


class DirectLcnfExecutableAdapter:
    """One per-case protocol executable over the direct-LCNF corpus."""

    def __init__(self, name: str, target: str, *, lcnf_coverage: bool) -> None:
        self.name = name
        self.target = target
        self.lcnf_coverage = lcnf_coverage
        self.root: Path | None = None
        self.executable: Path | None = None
        self.tool: ValidationTool | None = None

    def prepare_manifest(self, descriptors: list[dict]) -> list[dict]:
        return prepare_manifest(descriptors) if self.lcnf_coverage else descriptors

    def build(self, context: BuildContext) -> None:
        self.root = None
        self.executable = None
        self.tool = None
        if not context.no_build:
            built = run(["lake", "build", self.target], context.root)
            if built.returncode != 0:
                sys.stderr.write(built.stdout + built.stderr)
                raise ValidationError(
                    f"failed to build {self.name} validation backend"
                )
        self.executable = resolve_lake_command(context.root, self.target)
        self.root = context.root
        self.tool = validation_tool_from_file(
            self.name,
            "executable",
            f".lake/build/bin/{self.target}",
            self.executable,
        )

    def verify_tool(self) -> None:
        if self.executable is None or self.tool is None:
            raise ValidationError(
                f"{self.name} adapter must be built before execution"
            )
        current = validation_tool_from_file(
            self.name,
            self.tool.kind,
            self.tool.name,
            self.executable,
        )
        if current != self.tool:
            raise ValidationError(
                f"{self.name} validation executable changed during run"
            )

    def manifest(self) -> list[dict]:
        self.verify_tool()
        if self.executable is None or self.root is None:
            raise ValidationError(
                f"{self.name} adapter must be built before manifest discovery"
            )
        command = [str(self.executable), "--manifest"]
        completed = run(command, self.root)
        self.verify_tool()
        if completed.returncode != 0:
            raise ValidationError(
                f"failed to read {self.name} corpus manifest:\n"
                f"{completed.stderr}"
            )
        return manifest_from_output(completed.stdout, command)

    def execute(self, context: RunContext) -> BackendRun:
        self.verify_tool()
        if self.executable is None or self.tool is None:
            raise ValidationError(
                f"{self.name} adapter must be built before execution"
            )
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
                records_from_output(completed.stdout, command),
                self.name,
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
        if not self.lcnf_coverage:
            return BackendAudit()
        report, findings = coverage_report(
            context.descriptors,
            backend_run.results,
            context.selected,
            backend=self.name,
        )
        write_coverage_artifact(context.out_dir / self.name, report)
        return BackendAudit(report, findings)


DIRECT_NATIVE_ADAPTER = DirectLcnfExecutableAdapter(
    "direct-native",
    "fir-direct-native",
    lcnf_coverage=False,
)

DIRECT_LCNF_ADAPTER = DirectLcnfExecutableAdapter(
    "direct-lcnf",
    "fir-direct-lcnf",
    lcnf_coverage=True,
)
