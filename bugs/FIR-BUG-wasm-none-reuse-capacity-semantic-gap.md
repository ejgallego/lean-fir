---
id: FIR-BUG-wasm-none-reuse-capacity-semantic-gap
status: confirmed
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
`WasmSupported` currently admits such a program.

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

The regression checks that the program is accepted by `supportedProgram`,
that FIR returns tagged value `71`, and that the concrete target traps on the
capacity check.

## Expected semantics

For every program admitted by the Wasm proof fragment, an in-place reuse must
either be known to fit the retained allocation or both source and target must
agree on a structured failure.

## Actual behavior

`Fir.LeanIR.Impure.reuse` has no allocation-size state and succeeds after the
token, arity, liveness, and constructor checks. `reuseObject` retains the old
physical extent and returns a target-classified
`reuseAllocationTooSmall` failure when
`ConstructorLayout.ofInfo replacement` does not fit.

The successful refinement theorem
`LiveHeapRel.reuseObject_some_refines` exposes the missing condition as its
explicit `layoutFits` premise, but `WasmSupported` does not establish that
premise for arbitrary accepted reset/reuse code.

## Proof or differential evidence

The executable regression crosses FIR interpretation, lowering, Talos
adaptation, concrete host resolution, and concrete execution. It demonstrates
a successful source result paired with a target-only trap, so no
`ConcreteErrorSourceRel` workaround is possible.

## Semantic impact

The current successful W6 theorem cannot be made total over all
`WasmSupported` reset/reuse programs. This is a target-safety/completeness gap,
not a source structured-fault case.

## Classification and triage

Generated Lean reset/reuse patterns may carry a stronger capacity invariant
than the current boolean validator records. The clean repair is to derive and
validate that invariant, or to enrich FIR's reuse semantics with the physical
capacity decision. Silently allocating fresh storage would change the native
reuse protocol and must not be assumed without a contract decision.

## Workaround

Keep `layoutFits` explicit in reuse refinement theorems and restrict positive
claims to compiler-derived or otherwise proved fitting replacements. Do not
reclassify this target memory failure as a source fault.

## Upstream tracking

none

## Resolution and regression

unresolved
