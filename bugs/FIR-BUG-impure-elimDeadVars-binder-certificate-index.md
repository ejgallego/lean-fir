---
id: FIR-BUG-impure-elimDeadVars-binder-certificate-index
status: fixed
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: e64abaf
phase: impure
pass: elimDeadVars-0
discovered-by: proof
first-seen: 2026-07-25
reproduction: Fir/LeanIR/Passes/ElimDeadHygieneGraph.lean#ExactShadowCodeBinderReady
regression: Fir/LeanIR/Passes/ElimDeadHygieneGraph.lean#ExactShadowCodeBinderReady.letDeleted_ambientAbsent
---

# Summary

The proof-relevant hereditary binder-readiness certificate does not index its
deleted-let and deleted-join ambient-absence fields by the binder in the exact
compiler branch view.

## Minimal reproduction

Print the fully elaborated types of
`ExactShadowCodeBinderReady.letDeleted` and
`ExactShadowCodeBinderReady.joinDeleted`.  Each constructor contains two
independent binder variables: one hidden in the
`ExactShadowCodeView` result and another used by the recorded
`ambient.contains ... = false` field.

## Exact commands

```text
lake env lean /tmp/FirInspect.lean
```

The inspection file imports `ElimDeadHygieneGraph` and checks the two
constructors with explicit arguments.

## Expected semantics

A deleted-node certificate must state that the exact deleted let or join
binder is absent from the enclosing active liveness set.

## Actual behavior

The constructor can be instantiated with ambient absence for an unrelated
identifier while certifying an exact view that deletes a different binder.

## Proof or differential evidence

The elaborated let constructor contains both hidden declaration `x_5`, used
by `ExactShadowCodeView.letDeleted`, and explicit `declaration`, used only by
the ambient-absence premise.  The join constructor analogously contains
distinct hidden `x_9` and explicit `fvarId`.

## Semantic impact

The certificate is too weak to justify the deleted-let and deleted-join
machine rules.  Consuming it without repairing the index would make the
non-lockstep proof capable of assuming absence of the wrong binder.

## Classification and triage

This is a FIR proof-interface defect introduced by the new hereditary
certificate.  Lean 4.32's traversal branch data contains the correct binder;
the local inductive result failed to tie its explicit absence field to that
data.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

`ExactShadowCodeBinderReady` now supplies every source-operation parameter
explicitly to its exact-view index.  In particular, the deleted-let
declaration and deleted-join identifier used by the ambient-absence fields are
the same values carried by the certified compiler branches.

The projection theorems
`ExactShadowCodeBinderReady.letDeleted_ambientAbsent` and
`ExactShadowCodeBinderReady.joinDeleted_ambientAbsent` are kernel regression
guards: each can return absence only for the binder named by the exact
deleted branch.  `ExactShadowCodeView.reachableCodeReadyAt` then consumes those
indexed fields in the corresponding machine residuals.
