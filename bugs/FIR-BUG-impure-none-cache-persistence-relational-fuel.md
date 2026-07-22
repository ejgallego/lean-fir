---
id: FIR-BUG-impure-none-cache-persistence-relational-fuel
status: candidate
classification: fir-semantics
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: impure
pass: none
discovered-by: proof
first-seen: 2026-07-22
reproduction: Fir/LeanIR/Passes/ElimDeadMachineRel.lean
regression: none
---

# Summary

The cache-persistence operation uses whole-heap-length fuel, so two runtimes
that differ only by unreachable garbage execute related cache writes at
different recursive fuel indices with no theorem-grade relational interface.

## Minimal reproduction

Take two `ShadowRuntimeRel` runtimes whose reachable heaps are related by an
address renaming, but prepend one unmapped unreachable cell to the source
heap.  Yield related heap references over matching `.cache name` frames.
`coreStep` calls `RuntimeState.setGlobal` on both sides; its internal
`markPersistentLocationFuel` calls receive `source.heap.length + 1` and
`target.heap.length + 1`, which are unequal despite the extra cell being
semantically irrelevant.

## Exact commands

Run:

```text
lean-beam update Fir/LeanIR/Passes/ElimDeadMachineRel.lean
lean-beam sync Fir/LeanIR/Passes/ElimDeadMachineRel.lean
```

Then attempt the yielded-cache case of `ReachableMachineRelated`: relate
`source.runtime.setGlobal name sourceValue` to
`target.runtime.setGlobal name targetValue` using only the existing
`ShadowRuntimeRel` and `ValueRel` hypotheses.

## Expected semantics

Recursive persistence should be equivariant under the address renaming on
the reachable object graph.  Unreachable garbage and its contribution to the
whole heap length should not affect the resulting reachable cells, globals,
world, or trace.

## Actual behavior

`markPersistentLocationFuel` is transparent, but its only public equations
are tied to a concrete natural-number fuel.  `RuntimeState.markPersistent`
chooses fuel from the complete heap length.  `ShadowRuntimeRel` deliberately
does not equate complete heaps or their lengths, so a structural lockstep
induction cannot align the two calls and no extensional persistence theorem
is currently available.

## Proof or differential evidence

The reachable `elimDeadVars` simulation now proves yielded bind and apply
frames, but the corresponding cache-frame obligation stops before constructing
the post-step `ShadowRuntimeRel`: source and target persistence traversals have
different fuel indices even though the yielded roots are `ValueRel` and are
already included in the relation's runtime roots.

## Semantic impact

This blocks the general reachable-runtime proof for cache frames and therefore
for nullary internal declaration calls.  It does not currently demonstrate an
execution mismatch; identical runtimes remain covered by the older
exact-runtime proof.

## Classification and triage

This is provisionally a FIR semantic proof-interface defect.  The preferred
fix is an extensional theorem characterizing `markPersistentLocationFuel` once
fuel is sufficient for the reachable graph, followed by a
`ShadowRuntimeRel.setGlobalBoth` theorem that is insensitive to unreachable
heap padding.  A semantic mismatch remains possible if unequal sufficient
fuel values can produce different reachable metadata and should be tested
while proving that theorem.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

unresolved
