---
id: FIR-BUG-wasm-none-constructor-refinement-field-kinds
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: b73f18a
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/HeapRefinement.lean
regression: Fir/Wasm/Concrete/HeapRefinement.lean
---

# Summary

The concrete constructor refinement constrains the field-kind array's length
but does not require its entries to be ABI-admissible object-field kinds.

## Minimal reproduction

Instantiate `allocateConstructor_nonempty_objectRel` with an `info.size = 1`
constructor and `fieldKinds = #[.uint32]`. The theorem accepts that descriptor
when supplied a matching scalar `ValueRel`, even though
`AbiKind.isObjectField .uint32` is false and the executable ownership runtime
will later interpret the stored 32-bit scalar word as a possible object
reference.

## Exact commands

Inspect `ConstructorObjectRel` in `Fir/Wasm/Concrete/HeapRefinement.lean` and
the premises of `allocateConstructor_nonempty_objectRel` in
`Fir/Wasm/Concrete/ConstructorAllocationCorrectness.lean`. They require
`fieldKinds.size = info.size` but contain no `fieldKinds.all
AbiKind.isObjectField = true` invariant. Attempting to prove that every
`readOwnedReferences` result relates to a semantic owned value exposes the
missing premise.

## Expected semantics

The frozen Wasm ABI and `supportedLetDeclKind?` require every constructor
object slot to satisfy `AbiKind.isObjectField`. Consequently recursive release
may interpret those words only as heap references, tagged references, or the
erased sentinel.

## Actual behavior

The heap relation and its allocation theorem admit scalar ABI kinds in object
slots. Depending on the scalar bits, recursive concrete release can skip the
word, reject it, or treat it as a heap address, none of which is justified by
the semantic scalar value.

## Proof or differential evidence

The constructor owned-reference decoder proof obtains a `ValueRel` for each
word but cannot rule out its `.uint8`, `.uint16`, or `.uint32` cases. Those
cases have no uniform correspondence with the semantic recursive-release
fold, which only follows `.object (.heap child)` values.

## Semantic impact

The executable compiler rejects the ill-typed descriptors, but the current
W6 heap refinement is too weak to prove recursive release correct for the
states it claims to relate. Adding a side condition only to the final release
theorem would leave the global invariant unsound and non-compositional.

## Classification and triage

This is a Wasm refinement-model defect rather than an observed compiler bug.
The ABI checker already enforces the missing fact; allocation and heap
relations must preserve it.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in W6.3p by adding `fieldKindsValid` to `ConstructorObjectRel` and
requiring constructor allocation to establish
`fieldKinds.all AbiKind.isObjectField = true`. Every constructor-preservation
proof transports the invariant. `ConstructorObjectRel.fieldKind` is the
per-index regression boundary: any declared object-slot index yields a stored
kind and a proof that the kind is ownership-admissible.
