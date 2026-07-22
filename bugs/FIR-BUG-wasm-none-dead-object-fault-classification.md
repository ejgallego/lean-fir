---
id: FIR-BUG-wasm-none-dead-object-fault-classification
status: fixed
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

Dereferencing a deleted mapped object is a source `deadObject location` fault
in FIR but a target-memory `deadObject address` failure in the concrete Wasm
host.

## Minimal reproduction

`deletedProgram` allocates a string, deletes it, and then asks `isShared` about
the stale reference. The semantic interpreter and complete concrete
lowering/adapter/host path execute the same closed program.

## Exact commands

Run `make talos-check`. Adjacent guards check the semantic source fault and the
concrete target-memory classification.

## Expected semantics

`getLiveCell` finds the released semantic cell and returns `.deadObject 0`.
Because the concrete address is related to location zero by the refinement
witness, the structured Wasm fault should remain source-classified after that
address is translated back through the witness.

## Actual behavior

`MemoryState.readLiveHeader` returns `MemoryError.deadObject address`.
`liftMemory` classifies every memory error as `ConcreteError.target`, so the
Talos host reports `.runtime (.target (.memory (.deadObject address)))`.

## Proof or differential evidence

`ConcreteRuntimeExamples.lean` guards both `faulted? (runMain deletedProgram)
(.deadObject 0)` and the complete concrete fixture's exact target-memory trap.

## Semantic impact

Complete structured-fault correspondence cannot cover stale references for
operations that decode live headers, including projection, mutation, sharing,
boxing-related reads, and ownership operations.

## Classification and triage

The semantic and concrete runtimes agree that the object is dead; only the
source/target classification and location/address payload differ. The Wasm
fault ABI likely needs an address-bearing `ConcreteAddressFault.deadObject`
case, with witness-indexed translation analogous to reference-count
underflow. Because this changes the semantic Wasm ABI, it should land as an
isolated shared-contract commit.

## Workaround

Keep stale-reference failures outside complete correspondence claims. Do not
reclassify all memory failures or weaken FIR's location-indexed fault.

## Upstream tracking

none

## Resolution and regression

Resolved in W6.6bl by adding `ConcreteAddressFault.deadObject`, mapping
`MemoryError.deadObject address` through `liftMemory` to `sourceAddress`, and
relating that address fault to `RuntimeFault.deadObject location` through
`HeapReferenceRel`. The closed `deletedProgram` regression now requires the
Talos host's source-address trap rather than the former target-memory trap.
