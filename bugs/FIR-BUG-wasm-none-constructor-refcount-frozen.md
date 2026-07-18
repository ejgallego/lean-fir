---
id: FIR-BUG-wasm-none-constructor-refcount-frozen
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/HeapRefinement.lean
regression: Fir/Wasm/Concrete/Examples.lean
---

# Summary

The decoded constructor payload relation incorrectly freezes the mutable concrete reference count at its allocation value of one.

## Minimal reproduction

Start from any nonempty constructor related by `LiveCellRel`, increment its semantic and concrete reference counts, and attempt to reconstruct `ConstructorObjectRel` for the unchanged payload. The relation simultaneously requires the new header count and `header.refCount.toNat = 1`.

## Exact commands

Run `lean-beam update Fir/Wasm/Concrete/ReferenceCountCorrectness.lean` and attempt the constructor case of a successful nonpersistent increment refinement.

## Expected semantics

Constructor layout, tag, and field decoding must remain stable while the mutable common-header reference count follows the semantic `HeapCell.rc`.

## Actual behavior

`ConstructorObjectRel.header` records `header.refCount.toNat = 1`, while the enclosing `LiveCellRel.constructor` separately and correctly records equality with the current semantic cell count.

## Proof or differential evidence

After writing `oldCount + amount`, all constructor payload reads frame correctly, but the payload relation can only be rebuilt by proving the new count is still one.

## Semantic impact

No nontrivial constructor increment or decrement can preserve the decoded live-heap relation, blocking W6.3 ownership refinement.

## Classification and triage

This is local to the Wasm proof model. The concrete header and FIR runtime both already treat reference counts as mutable; only the allocation-era payload invariant retained the stale equality.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in W6.3a by separating immutable constructor layout/payload facts
from mutable common-header ownership metadata. `ConstructorObjectRel` no
longer freezes the allocation-time count; `LiveCellRel` remains the single
relation tying the decoded header count to the semantic cell count.

Fresh constructor allocation still proves the exact initialized header, so
the change does not weaken its postcondition. `ReferenceCountCorrectness.lean`
now reconstructs a decoded boxed live cell after a nontrivial increment, and
`Fir.Wasm.Concrete.Examples` guards the same `1 + 2 = 3` transition while
checking that the payload remains decodable and `isShared` changes to true.
