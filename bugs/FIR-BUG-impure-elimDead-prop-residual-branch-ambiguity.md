---
id: FIR-BUG-impure-elimDead-prop-residual-branch-ambiguity
status: confirmed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: e64abaf
phase: impure
pass: elimDeadVars
discovered-by: proof
first-seen: 2026-07-25
reproduction: Fir/LeanIR/Passes/ElimDeadHygieneGraph.lean#exactShadowCodeGraph_deletedLet_absent
regression: none
---

# Summary

FIR's `Prop`-valued elimDead residual and proof-indexed `WasDeleted`
classifier cannot reliably identify the traversal branch that produced a
graph.

## Minimal reproduction

Construct the exact graph for a successful let traversal:

```lean
exactShadowCodeGraph result
```

Assume its proof-indexed residual satisfies:

```lean
(exactShadowCodeGraph result).letResidual.WasDeleted
```

Eliminating that witness recovers only a deletion-local liveness set and a
subset proof into the exact graph's final set.  It does not establish that
the two sets are equal, so the expected active-index obligation remains:

```text
final.contains declaration.fvarId = false
```

This is not merely a missing lemma. `ShadowLetResidual` is in `Prop`, so its
proof is proof-irrelevant.  If retained and deleted traversals produce the
same target code shape, a `WasDeleted` witness can be transported to the
proof returned by `graph.letResidual` without preserving branch provenance.
The join residual has the same issue.

## Exact commands

```text
lean-beam update Fir/LeanIR/Passes/ElimDeadHygieneGraph.lean
lean-beam sync Fir/LeanIR/Passes/ElimDeadHygieneGraph.lean
```

The sync stops at `exactShadowCodeGraph_deletedLet_absent`: after
`cases deleted`, Lean exposes `localAbsent` for `localUsed` and
`UsedSubset localUsed final`, but the goal concerns `final`.

## Expected semantics

An exact successful traversal should carry a proof-relevant branch witness.
Selecting the deleted constructor should identify the continuation result as
the parent's exact final liveness set, making decision-time binder absence
available at the active graph index.

## Actual behavior

`ShadowCodeGraph`, `ShadowLetResidual`, and `ShadowJoinResidual` are
`Prop`-valued. `WasDeleted` is indexed by a residual proof rather than by
proof-relevant traversal data. Its elimination therefore cannot recover
which computational branch produced the exact graph.

## Proof or differential evidence

The failed let obligation has context:

```text
localAbsent : localUsed.contains declaration.fvarId = false
localSubset : UsedSubset localUsed final
⊢ final.contains declaration.fvarId = false
```

The subset direction cannot prove nonmembership. In the retained join branch,
the analogous proof also cannot use `WasDeleted` to reject that branch.

## Semantic impact

This blocks constructing hereditary deleted-let and deleted-join readiness
from an exact transparent run. It does not demonstrate a Lean compiler
miscompilation; it is a FIR proof-interface defect that erases branch
provenance needed by the correctness proof.

## Classification and triage

Classified as `fir-semantics`: the ambiguity is introduced by FIR's
proof-valued residual interface, not by Lean 4.32's traversal. The existing
widened-liveness repair retains local absence but does not make traversal
branch selection proof-relevant.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Unresolved. Replace or supplement the proof-valued residual classifier with
a proof-relevant exact-run branch view, then prove that forgetting it yields
the existing monotone graph relation.
