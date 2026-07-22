---
id: FIR-BUG-wasm-none-uninitialized-scalar-projection
status: confirmed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: differential-test
first-seen: 2026-07-21
reproduction: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
regression: integration/talos/FirTalos/ConcreteRuntimeExamples.lean
---

# Summary

A layout-valid packed scalar projection before any matching write faults with
`scalarFieldMissing` in FIR but returns zero from the concrete Wasm heap.

## Minimal reproduction

`uninitializedScalarProjectionProgram` allocates `layoutInfo`, whose packed
region contains eight bytes, and immediately projects `UInt64` from the valid
compiler-shaped coordinate `(2, 0)` without an earlier `sset`.

## Exact commands

Run `make talos-check`. Adjacent guards execute the same closed program through
the FIR interpreter and the complete lowering/adapter/concrete-host path.

## Expected semantics

FIR constructor allocation initializes `ConstructorObject.scalarFields` to an
empty list. `getScalarField` therefore returns `scalarFieldMissing 2 0` until
`setScalarField` records that coordinate.

## Actual behavior

Concrete constructor allocation zero-fills the complete declared packed byte
region. `readScalarUInt64Field` validates only the layout coordinate and reads
those bytes, so the generated module returns `UInt64(0)` with no host failure.

## Proof or differential evidence

`ConcreteRuntimeExamples.lean` guards both observations: `faulted? (runMain
uninitializedScalarProjectionProgram) (.scalarFieldMissing 2 0)` and
`fixtureReturnsI64? uninitializedScalarProjectionProgram 0`.

## Semantic impact

Full structured-fault correspondence for `scalarProj` cannot be proved for
all programs currently admitted by the Wasm fragment. Successful
compiler-produced write/read sequences are unaffected.

## Classification and triage

The shared FIR runtime has a coherent dynamic-initialization contract, while
the concrete representation currently has no initialization bitmap or static
definite-write validation. The Wasm track must either represent initialized
packed coordinates or reject programs that can project them before a write.

## Workaround

Restrict positive concrete fixtures and claims to coordinates established by
an earlier `sset`; do not weaken FIR's missing-field fault.

## Upstream tracking

none

## Resolution and regression

unresolved
