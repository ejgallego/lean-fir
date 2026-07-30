---
id: FIR-BUG-wasm-none-reuse-retained-zero-empty-result
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: f41a651fa5704692159653a9addfc29c200181bd
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-29
reproduction: integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean
regression: integration/talos/FirTalos/ConcreteReuseCapacityCorrectness.lean
---

# Summary

A constructor with retained-capacity provenance may reset to the physical zero
token when it is shared or persistent. Reusing that token for an empty-layout
constructor takes the fresh tagged-allocation path. The static
`ReuseCapacityEvidence.afterReuse` transfer admits this execution, but the
dynamic `ReuseCapacityValueRel` relation had no retained-evidence constructor
for the resulting tagged object.

## Minimal reproduction

Track a nonempty constructor with `retainedAtLeast available`, reset it while
its source cell is shared or persistent, and then reuse the resulting
`.reuseToken none` with an empty-layout constructor descriptor.

The source and concrete runtimes both return a tagged constructor. The static
transfer records
`retainedAtLeast (ConstructorLayout.ofInfo info).allocationBytes`, whose
meaning is conditional on a later reset returning a nonzero token, but the
old dynamic relation required every retained-evidence object to be heap-backed.

## Exact commands

```text
lake env lean FirTalos/ConcreteReuseCapacityCorrectness.lean
make talos-check
```

## Expected semantics

`retainedAtLeast bytes` means that every nonzero reuse token later obtained
from the tracked value retains at least `bytes`. A tagged object always resets
to zero, so it satisfies this conditional claim vacuously.

## Actual behavior

`ReuseCapacityValueRel.retainedObject` required a mapped heap address and
readable header. No constructor represented a tagged object under retained
evidence, so the branch-independent successful-reuse theorem could not cover
this valid source and target execution.

## Proof or differential evidence

Case analysis on a retained empty token followed by an empty-layout reuse
reduces the operation to the existing tagged allocation refinement theorem.
Its result has an ordinary `ValueRel`, but no inhabitant of the validator's
selected post-fact relation.

## Semantic impact

Without the missing case, a whole-program capacity theorem would either omit a
successful supported execution or weaken the static transfer inconsistently.
The executable runtime behavior is already correct.

## Classification and triage

This is a refinement-model incompleteness in the W6 reuse-capacity relation,
not a source/target runtime mismatch.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

W6.6fy adds the tagged-object constructor for retained evidence and threads it
through witness/header transport and the projection back to ordinary
`ValueRel`. The branch-independent reuse theorem exercises the retained-zero,
empty-layout path and establishes the exact validator-selected `afterReuse`
fact.
