---
id: FIR-BUG-impure-elimDead-live-prefix-historical-target-heap
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.33.0
lean-revision: d8b18978322de05a8f3dba51ef03cf5461676c17
phase: impure
pass: elimDeadVars
discovered-by: proof
first-seen: 2026-08-26
reproduction: Fir/LeanIR/Passes/ElimDeadExamples.lean
regression: Fir/LeanIR/Passes/ElimDeadExamples.lean
---

# Summary

`TargetLiveHeapPrefixControlAt` cannot be derived for every structurally
related compiler residual.  The target allocation ledger records historical
allocations below the complete target frontier, while current code, frames,
and environments need name only reachable values.  An unreachable historical
target cell therefore need not have any current live binder.

## Minimal reproduction

`historicalTargetHeapHasNoDirectLivePrefix` constructs an active return state
whose runtime contains two allocated cells but whose environment names only
location `0`.  No binder family can satisfy `targetRead` for location `1`,
even though the active residual and the retained location are otherwise
ordinary.

## Exact commands

From `.worktrees/proof-simpcase`, with the FIR Lake artifact-cache variables
and worktree-local `TMPDIR` required by `AGENTS.md`:

```text
lean-beam update Fir/LeanIR/Passes/ElimDeadExamples.lean
lean-beam sync Fir/LeanIR/Passes/ElimDeadExamples.lean
lake build +Fir.LeanIR.Passes.ElimDeadExamples
```

## Expected semantics

Deleted reset/reuse readiness should distinguish the source-only owned
closure from target locations that remain semantically reachable.  It should
not require every historical target allocation to be named directly by the
current residual code.

## Actual behavior

The generic live-prefix adapter quantifies over every location below
`target.runtime.nextLocation`.  That is valid for the focused retained-prefix
fixture, but stronger than the general runtime relation and allocation-ledger
contract.

## Proof or differential evidence

The kernel regression proves the direct live-prefix proposition is false for
the two-cell historical target shape.  No executable mismatch is known; this
is a limitation in the proof interface exposed to general compiler clients.

## Semantic impact

Automatically deriving the current live-prefix certificate from
`CodeCovered`, `EnvRelOn`, and `ShadowRuntimeRel` would be unsound.  A general
ElimDead reset/reuse proof needs a source-only closure capability created at
the one-sided allocation and transported through later ledger extensions.

## Classification and triage

This is a proof-coverage gap, not a compiler workaround request.  Preserve
the exact target allocation ledger, but carry selected source-only closure
provenance through its lifecycle rather than weakening the ledger or
inventing bindings for unreachable target cells.

## Workaround

The canonical retained-prefix fixture now stores only its target execution
path in the rectangular contract and reconstructs the focused phase
certificate at the special reset/reuse nodes.  This removes the duplicated
client invariant but deliberately does not claim a general live-prefix
derivation.

## Upstream tracking

none

## Resolution and regression

Open.  The permanent resolution is a ledger-aligned source-only closure
carrier that survives same-frontier operations and paired allocations.  The
historical-target negative regression must remain after that carrier replaces
the focused live-prefix adapter.
