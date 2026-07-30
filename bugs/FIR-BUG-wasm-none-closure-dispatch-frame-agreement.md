---
id: FIR-BUG-wasm-none-closure-dispatch-frame-agreement
status: candidate
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 791f2ac1c0ae89237e279df32cddeabd4a3c5722
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-30
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
regression: none
---

# Summary

The canonical W6 reuse/capacity/cache frame preserves equality between the
concrete host and refinement-witness closure descriptor tables, but does not
retain equality between their closure dispatch tables. Constructively deriving
the generated saturated-closure matcher result therefore reaches a missing
invariant even though both tables originate from the same source module and
the executable runtime operations leave them immutable.

## Minimal reproduction

Start from a `ConcreteReuseCapacityCacheFrame` and resolve a source local that
contains a semantic closure to its concrete heap address. Applying
`closureMatchesStep_of_refines` to prove the generated candidate matcher asks
for

```text
initialWitness.closureDispatch = initial.host.closureDispatch
```

The frame exposes the corresponding closure-descriptor equation, but no
dispatch-table equation.

## Exact commands

```text
rg -n "ConcreteReuseCapacityPureExternalOwnershipFrame|closureDispatch" \
  integration/talos/FirTalos/ConcreteCompilerCorrectness.lean \
  integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean
rg -n "closureMatchesStep_of_refines" \
  integration/talos/FirTalos/ConcreteRuntime.lean
```

## Expected semantics

The program-entry relation should retain both immutable module-derived closure
tables and every runtime transport should preserve them. A concrete closure
related to a source closure can then classify each generated matcher directly
from its function name, total arity, and fixed-capture count.

## Actual behavior

Only `closureDescriptors` equality is threaded through the canonical frame and
the budgeted declaration/runtime transport interfaces. The current
`SaturatedClosureDispatchSelectionInduction` can hide the missing equation by
accepting each `ClosureCandidateCase.operation` as an induction premise.

## Proof or differential evidence

`closureMatchesStep_of_refines` already proves the exact executable matcher
result from `ConcreteRuntimeRel`, source closure-cell facts, and equality of
both immutable tables. The dispatch-table premise cannot be recovered from the
current cache frame. Initial adapter construction and all concrete host
operations inspected so far preserve the dispatch table; the loss is in the
composed proof invariant.

## Semantic impact

No executable mismatch is known. The missing relation blocks a
certificate-free proof of generated saturated closure selection: without it,
an arbitrary host dispatch table could disagree with the refinement witness
while satisfying the current frame.

## Classification and triage

This is a W6 Wasm-adapter proof-invariant omission, not a source-language or
linear-memory layout discrepancy. The repair should strengthen the shared W6
entry/transport frame rather than postulate matcher outcomes at individual
call sites.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. Add dispatch-table agreement to the canonical frame and transport
it through direct operations, effects, calls, lazy-cache paths, and hereditary
declaration results. The regression should construct the generated
first-matching saturated closure candidate without a caller-supplied target
matcher execution.
