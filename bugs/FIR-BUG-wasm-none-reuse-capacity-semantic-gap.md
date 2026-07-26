---
id: FIR-BUG-wasm-none-reuse-capacity-semantic-gap
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-24
reproduction: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
regression: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
---

# Summary

FIR's semantic `reuse` replaces a retained constructor cell without tracking
its physical allocation capacity. The concrete Wasm runtime correctly refuses
an in-place replacement whose layout is larger than that allocation.
Before W6.6df, `WasmSupported` admitted such a program.

## Minimal reproduction

Allocate a one-field constructor, uniquely reset it, then reuse the nonempty
token with a two-field constructor descriptor. Both descriptors otherwise use
the same supported object-only layout.

The source interpreter replaces the semantic cell and returns its first new
field. The concrete runtime compares the two-field layout with the retained
one-field allocation and returns
`MemoryError.reuseAllocationTooSmall available required`.

## Exact commands

Run:

```text
make talos-check
```

The regression checks that `supportedProgram` and `validateSupported` now
reject the program, that FIR still returns tagged value `71`, and that raw
lowering reaches the exact concrete capacity trap. Adjacent positive
regressions retain fitting, shared-reset, and definitely-empty-token growth.

## Expected semantics

For every program admitted by the Wasm proof fragment, an in-place reuse must
either be known to fit the retained allocation or both source and target must
agree on a structured failure.

## Actual behavior

At discovery, `Fir.LeanIR.Impure.reuse` had no allocation-size state and
succeeded after the
token, arity, liveness, and constructor checks. `reuseObject` retains the old
physical extent and returns a target-classified
`reuseAllocationTooSmall` failure when
`ConstructorLayout.ofInfo replacement` does not fit.

The successful refinement theorem
`LiveHeapRel.reuseObject_some_refines` exposes the missing condition as its
explicit `layoutFits` premise, but `WasmSupported` does not establish that
premise without the W6.6df capacity analysis.

## Proof or differential evidence

The executable regression crosses FIR interpretation, lowering, Talos
adaptation, concrete host resolution, and concrete execution. It demonstrates
a successful source result paired with a target-only trap, so no
`ConcreteErrorSourceRel` workaround is possible.

## Semantic impact

Without a retained-capacity gate, the successful W6 theorem cannot be made
total over all otherwise-supported reset/reuse programs. This is a
target-safety/completeness gap, not a source structured-fault case.

## Classification and triage

Generated Lean reset/reuse patterns carry enough local provenance for a
conservative capacity analysis. The validator must reject a reuse when its
token has no tracked reset provenance, or when the replacement exceeds the
tracked lower bound. Silently allocating fresh storage would change the native
reuse protocol and is not part of the repair.

## Workaround

Keep `layoutFits` explicit in reuse refinement theorems and restrict positive
claims to compiler-derived or otherwise proved fitting replacements. Do not
reclassify this target memory failure as a source fault.

## Upstream tracking

none

## Resolution and regression

Resolved in W6.6df by adding `reuseCapacitySafeProgram` to
`WasmSupported`. Direct constructor allocation records either a definitely
empty token or the concrete wasm32 allocation size. Reset transports that
evidence to its token, and a successful fitting reuse records the replacement
layout as the lower bound for a later reuse.

`findFittingReuseCapacityEvidence?_retained_layoutFits` exposes the exact
static consequence consumed by the existing
`LiveHeapRel.reuseObject_some_refines` premise. The supported validator now
rejects the one-field-to-two-field reproduction, while raw lowering still
executes it as a regression oracle and reaches the exact
`reuseAllocationTooSmall` target trap. The fitting and shared-reset positive
programs remain admitted.

The analysis is intentionally conservative: unknown object provenance and
join-parameter token transport are rejected when they feed reuse. That surface
is experimental and may be widened when a corresponding provenance theorem is
available.
