---
id: FIR-BUG-wasm-none-missing-tmpdir-lake-launch
status: closed-not-a-bug
classification: validation-harness
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-09-09
reproduction: FirValidationWasm.lean
regression: none
---

# Summary

The CG-01 integration gate initially failed because its caller selected a
nonexistent worktree-local TMPDIR, not because of the capture extraction.

## Minimal reproduction

In the integration worktree at 0895d974, the caller exported
TMPDIR=$PWD/.deps/tmp without first creating that directory. W7 had created
its own directory and passed all gates. This operational difference caused
the apparent worktree-specific regression.

## Exact commands

With TMPDIR pointing to a nonexistent worktree-local path:

```bash
lake --no-cache lean FirValidationWasm.lean
```

A read-only strace of that invocation records the failed temporary-file
creation. Do not remove a live temporary directory to reproduce this; use
an absent child under the worktree's ignored .deps instead.

## Expected semantics

The validation backend should compile the source with unchanged semantics.
A missing temporary directory is an invalid launcher configuration.

## Actual behavior

Lake exits 139 before producing diagnostics. The final syscall before the
signal is openat of a temporary setup file under the missing TMPDIR, returning
ENOENT. Direct lake env lean succeeds because it does not create that setup
file. An explicit 24-job dependency build also succeeds.

## Proof or differential evidence

All 23 imported FIR modules have identical olean and ilean hashes in W7 and
integration. W7's complete make check, Talos and artifact gates pass; all
239 existing Wasm/LCNF files compare unchanged. Diagnostic evidence is in
integration's .deps/cg01-lake-lean.trace and .deps/cg01-lake-backtrace.log.

## Semantic impact

None established. This is not evidence of a compiler import, artifact-cache,
runtime, or generated-code regression. The initial integration command was
misconfigured.

## Classification and triage

Closed as a caller setup mistake. Lake's handling of the failed temporary-file
creation could separately be improved upstream, but no upstream fix is part
of CG-01.

## Workaround

Create the selected directory before invoking the gate:

```bash
mkdir -p .deps/tmp
export TMPDIR="$PWD/.deps/tmp"
make check
```

## Upstream tracking

none

## Resolution and regression

No FIR source repair or permanent semantic fixture is warranted. The corrected
integration command creates the directory before use; preserve this card to
explain the initially failed gate rather than erase its evidence.
