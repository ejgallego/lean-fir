---
id: FIR-BUG-impure-elimDead-widened-liveness-witness
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: e64abaf
phase: impure
pass: elimDeadVars
discovered-by: proof
first-seen: 2026-07-25
reproduction: Fir/LeanIR/Passes/ElimDeadProgram.lean#ShadowCodeGraph.mono
regression: Fir/LeanIR/Passes/ElimDeadProgram.lean#ShadowLetResidual.localGraph_of_wasDeleted
---

# Summary

FIR's monotone `ShadowCodeGraph` proof interface permits a deleted binder to
be inserted into the graph's active liveness witness, making the current
proof-independent deleted-let readiness obligation unprovable even for
hygienic compiler input.

## Minimal reproduction

Start with the transparent graph for an erased dead let:

```text
let dead := erased
return live
```

The traversal deletes `dead` because the continuation result does not contain
it.  Given any corresponding
`ShadowCodeGraph fuel used source target`, apply
`ShadowCodeGraph.mono (usedSubset_insert used dead)`.  The result is another
valid graph for the same source and target, now indexed by
`used.insert dead`, where `contains dead = true`.

`ReachableMachineReadyAt` quantifies over every proof-valued structural
decomposition.  Its deleted-let branch requires
`used.contains dead = false`, so the widened graph supplies a legal
structural witness for which readiness cannot be constructed.

## Exact commands

```text
rg -n "def ShadowCodeGraph|theorem ShadowCodeGraph.mono|def ReachableMachineReadyAt" \
  Fir/LeanIR/Passes/ElimDeadProgram.lean \
  Fir/LeanIR/Passes/ElimDeadMachineRel.lean
lake build Fir.LeanIR.Passes.ElimDeadMachineRel
```

Then instantiate `ShadowCodeGraph.mono` with
`usedSubset_insert used declaration.fvarId` at a deleted-let graph and attempt
to satisfy the universal `ReachableMachineReadyAt` obligation.

## Expected semantics

Readiness should be checked against the deletion-local continuation liveness
set produced by the pinned traversal, or against an aligned structural
witness that preserves that provenance.  The deleted binder is absent from
that local set by construction.  Compiler hygiene is then responsible only
for proving that legitimate enclosing traversal growth cannot reintroduce the
globally fresh binder.

## Actual behavior

`ShadowCodeGraph` remembers only that the traversal's final set is a subset of
the exposed `used` index.  `ShadowCodeGraph.mono` therefore accepts arbitrary
growth, including the deleted binder itself.  The first repair now retains
the exact continuation set and its nonmembership proof in every deleted
residual, but the outer readiness interface does not yet use that provenance
in place of its exposed-set absence premise.

At the machine layer, `ReachableMachineReadyAt` universally quantifies over
all hidden root/control/frame witnesses so readiness cannot select the
deletion-local graph.  No program-hygiene theorem can prove nonmembership in
an arbitrary hash-set superset.

## Proof or differential evidence

The failed obligation is:

```text
used.contains declaration.fvarId = false
```

for the `ReachableLetReadyAt.deleted` constructor.  For
`used := originalUsed.insert declaration.fvarId`, simplification proves the
opposite equality.  The widened graph remains valid solely through
`ShadowCodeGraph.mono`; it does not correspond to additional compiler
analysis.

This is independent of
`FIR-BUG-impure-elimDeadVars-nullary-fap-effects`: erased lets are
operationally neutral, and the blocker is only the relation's witness
interface.

## Semantic impact

The issue blocks deriving hereditary entry readiness from
`WellFormedAt .impure`, and therefore blocks closing the whole-program
correctness theorem.  It does not demonstrate a Lean compiler
miscompilation; it demonstrates that FIR's current proof relation admits
strictly more liveness witnesses than the compiler traversal produces.

## Classification and triage

Classified as a FIR-semantics proof-interface defect.  Lean 4.32's traversal
tests deletion against its exact continuation result.  FIR intentionally
introduced the monotone superset index to make join and alternative graphs
share one environment relation, but the later universal readiness layer made
that convenience observable.

The preferred repair is to retain deletion-local liveness provenance in the
residual or to bundle readiness with an aligned structural witness.  Simply
assuming binder absence, removing the operational premise, or claiming
hygiene excludes membership in arbitrary supersets would be unsound.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Partially repaired: `ShadowLetResidual.deleted` now retains a deletion-local
continuation graph, its subset relation to the exposed graph, and the local
binder nonmembership proof.
`ShadowLetResidual.localGraph_of_wasDeleted` is the proof-level regression
boundary.  The aligned machine-readiness repair remains unresolved.
