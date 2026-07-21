---
id: FIR-BUG-wasm-none-scalar-slot-layout-contract
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-21
reproduction: Fir/Wasm/Examples.lean
regression: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
---

# Summary

The accepted hand-written scalar-mutation fixture uses a scalar slot index
that disagrees with its constructor layout, so semantic-host execution
succeeds while the concrete W6 host reports `scalarFieldMissing`.

## Minimal reproduction

`Fir.Wasm.abiMutationProgram` allocates `layoutInfo`, whose one object field
and one `USize` field require scalar slot index `2`, but its `sset` and `sproj`
operations use index `1` and offset `0`.

## Exact commands

Run `make talos-check`. The focused regression resolves and executes
`abiMutationProgram` against the concrete host and checks the structured
`scalarFieldMissing 1 0` failure.

## Expected semantics

Lean 4.32's `LCNF.ToImpure` emits scalar indices as
`ctorInfo.size + ctorInfo.usize`; for `layoutInfo`, both operations should use
index `2`. A program admitted as compiler-shaped should maintain that layout
invariant, or validation should reject it before execution.

## Actual behavior

FIR's semantic interpreter treats `(index, offset)` only as a key in its
abstract `scalarFields` list, so the write at `(1, 0)` creates a field and the
matching read returns `66`. The concrete layout derives the scalar payload
base from the constructor header and rejects index `1` because the fixed-slot
prefix has length `2`.

## Proof or differential evidence

`FirTalos.Concrete.fixtureReturnsI64? abiMutationProgram 66` fails with the
concrete host trap `scalarFieldMissing 1 0`. The existing W6 scalar mutation
theorems expose the missing invariant explicitly as
`slotIndex = info.size + info.usize`.

## Semantic impact

Whole-module concrete execution cannot cover every program currently accepted
by `supportedProgram`. Compiler-produced scalar operations remain unaffected,
but hand-written FIR and validation fixtures can cross the semantic/concrete
boundary with inconsistent layout metadata.

## Classification and triage

Lean 4.32 generation already emits the concrete host's required index. The
remaining gap is local to FIR's admitted Wasm fragment and its hand-written
fixture: validation does not connect a scalar operation to the target
constructor descriptor. The integration owner should decide whether to repair
the shared fixture, strengthen supported-fragment validation, or document a
descriptor-indexed precondition at the program boundary.

## Workaround

Retain the inconsistent fixture as an expected-failure regression and use a
separate index-`2` fixture for positive concrete execution coverage.

## Upstream tracking

none

## Resolution and regression

unresolved
