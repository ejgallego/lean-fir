---
id: FIR-BUG-wasm-none-constructor-arity-fault-classification
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

A constructor allocation with the wrong number of object fields is a broad
`malformed` fault in FIR but a dedicated source `arityMismatch` fault in the
concrete Wasm runtime.

## Minimal reproduction

`projectionInfo` declares one object field. Calling both allocators with an
empty field array makes semantic `allocCtor` return `.malformed ...` and the
concrete Talos allocation host return
`.source (.runtime (.arityMismatch 1 0))`.

## Exact commands

Run `make talos-check`. Adjacent guards execute the semantic allocator and the
concrete Talos host with the same expected/actual field counts.

## Expected semantics

The source and concrete fault boundary should agree on one structured fault
for the same invalid allocation request, including expected and actual counts
when that detail is part of the chosen contract.

## Actual behavior

`Fir.LeanIR.Impure.allocCtor` constructs
`RuntimeFault.malformed "constructor ... expected 1 object fields, got 0"`.
`Fir.Wasm.Concrete.allocateConstructor` constructs
`ConcreteError.source (RuntimeFault.arityMismatch 1 0)`, which Talos preserves
as a source runtime trap.

## Proof or differential evidence

`ConcreteRuntimeExamples.lean` guards the two distinct constructors directly.
No exact `ConcreteErrorSourceRel` proof can identify them.

## Semantic impact

Full structured-fault correspondence for `allocCtor` cannot include invalid
field counts. Valid compiler-produced allocation calls are unaffected because
validation aligns the descriptor and argument arities.

## Classification and triage

This is a shared source/concrete error-contract mismatch. Choose either the
dedicated `arityMismatch` payload or the semantic `malformed` message, then
change the other side in an isolated shared-contract commit.

## Workaround

Keep malformed constructor arities outside complete correspondence claims; do
not coerce unrelated fault constructors in the refinement relation.

## Upstream tracking

none

## Resolution and regression

unresolved
