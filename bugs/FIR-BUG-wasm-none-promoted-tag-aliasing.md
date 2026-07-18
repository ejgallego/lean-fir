---
id: FIR-BUG-wasm-none-promoted-tag-aliasing
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: proof
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/Refinement.lean
regression: Fir/Wasm/Concrete/Examples.lean
---

# Summary

The refinement witness models a promoted tagged payload with only one concrete address even though repeated encoding allocates a fresh address each time.

## Minimal reproduction

Call `encodeTagged` twice with the same payload above `maxImmediatePayload`. Both calls allocate persistent natural objects, but prepending the second `(payload, address)` pair to `RefinementWitness.promotedTags` makes `PromotedTags.lookup?` forget the first address.

## Exact commands

Run `lean-beam update Fir/Wasm/Concrete/Refinement.lean` and attempt to prove that `witness.Extends (witness.promoteTag payload address)` without assuming that the payload is absent from the old witness.

## Expected semantics

Every returned concrete word must continue to refine the same semantic tagged value after later allocations, including a later encoding of an equal payload.

## Actual behavior

The second binding shadows the first payload-to-address lookup, so an existing `TaggedReferenceRel.promoted` proof cannot be transported through the witness extension.

## Proof or differential evidence

The promoted-tag allocation refinement requires an unconditional witness-extension theorem, but the `promotedTags` field of `RefinementWitness.Extends` is false for a repeated payload with a different fresh address.

## Semantic impact

The current relation cannot prove environments or heap fields containing the first promoted representation remain valid after the same large tagged payload is boxed again.

## Classification and triage

This is local to the Wasm refinement model. The concrete runtime correctly permits multiple immutable representations of one tagged value; the ghost relation incorrectly assumes a partial function from payloads to addresses.

## Workaround

none

## Upstream tracking

none

## Resolution and regression

Resolved in W6.2j by replacing the partial payload-to-address ghost lookup
with a many-address membership relation. `RefinementWitness.promoteTag_extends`
now retains every old representation, including an equal payload at a distinct
address, while descriptor freshness preserves address-to-payload uniqueness.

`Fir.Wasm.Concrete.Examples` allocates the same promoted payload twice, decodes
both words after the second allocation, and proves both address memberships
remain present in the extended witness.
