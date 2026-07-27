---
id: FIR-BUG-impure-elimDead-source-ready-witness-reselection
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: e64abaf
phase: impure
pass: elimDeadVars
discovered-by: proof
first-seen: 2026-07-27
reproduction: Fir/LeanIR/Passes/ElimDeadMachineRel.lean#SourceRuntimeOwnershipReadyAt.not_fap_of_deleted
regression: Fir/LeanIR/Passes/ElimDeadMachineRel.lean#SourceRuntimeOwnershipReadyAt.not_fap_of_deleted
---

# Summary

FIR's first source runtime-readiness interface could rebuild readiness from a
different existential exact traversal witness instead of certifying the
proof-relevant compiler edge supplied by the structural relation.

## Minimal reproduction

Assume `SourceRuntimeOwnershipReadyAt` for an active full-application let and
apply it to a `BinderReadyShadowCodeGraph` whose operational residual has a
`WasDeleted` witness. Convert the returned
`BinderReadyShadowCodeReadyAt` to `ReachableCodeReadyAt` and invert it.

The returned readiness may select the retained-let constructor even though
the input graph was classified as deleted. The source and target code indices
can coincide with both a retained traversal and a deletion whose compiled
continuation happens to have the same outer let shape.

## Exact commands

```text
lean-beam update Fir/LeanIR/Passes/ElimDeadMachineRel.lean
lean-beam sync Fir/LeanIR/Passes/ElimDeadMachineRel.lean
```

The attempted
`SourceRuntimeOwnershipReadyAt.not_fap_of_deleted` theorem leaves an
unprovable retained branch after eliminating the deleted input residual.

## Expected semantics

The source invariant must provide `ExactShadowCodeRuntimeReadyAt` for the
same proof-relevant `ExactShadowCodeGraph.view` carried by the strong
structural relation. A deleted full application then immediately yields the
impossible `DeletedLetReadyAt` obligation.

## Actual behavior

The original interface had the shape:

```text
BinderReadyShadowCodeGraph ... -> BinderReadyShadowCodeReadyAt ...
```

Both sides are propositions containing existential exact witnesses. Proof
irrelevance prevents the result from being tied to the input witness, so the
client can satisfy the result with another traversal branch having the same
public source, target, fuel, and liveness indices.

## Proof or differential evidence

The retained inversion branch contains both:

```text
ready : RetainedLetReadyAt ... (.fap name arguments)
deleted : inputGraph.toShadowCodeGraph.letResidual.WasDeleted
```

but no equality connecting the returned exact view to `inputGraph`'s exact
view. The target code is an outer let, while the deleted graph's continuation
may also compile to that outer let, so the public indices alone do not reject
the branch.

## Semantic impact

The interface could conceal the known nullary-`.fap` compiler discrepancy and
could certify any dynamic branch using facts proved for a different exact
traversal. This is a FIR proof-interface defect, not new evidence of an
additional Lean compiler miscompilation.

## Classification and triage

Classified as `fir-semantics` because FIR erased exact witness alignment at
the boundary between hereditary structure and source runtime readiness. The
repair is to expose the exact graph, subset, and binder certificate to the
source invariant and ask directly for runtime readiness of that exact view.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Fixed by changing `SourceRuntimeOwnershipReadyAt` to accept the bounded
proof-relevant `ExactShadowCodeGraph`, its liveness subset, and its hereditary
binder certificate, and to return `ExactShadowCodeRuntimeReadyAt` for that
same `exact.view`. The machine-readiness bridge now reconstructs the strong
ready graph around that aligned view.

`SourceRuntimeOwnershipReadyAt.not_fap_of_deleted` is the permanent
regression: when the exact view's runtime decision is `deletedLet`, rewriting
the aligned runtime obligation exposes `DeletedLetReadyAt`, whose `.fap`
inversion is contradictory.
