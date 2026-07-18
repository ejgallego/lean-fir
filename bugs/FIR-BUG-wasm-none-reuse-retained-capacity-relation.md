---
id: FIR-BUG-wasm-none-reuse-retained-capacity-relation
status: fixed
classification: wasm-adapter
lean-toolchain: leanprover/lean4:v4.32.0
lean-revision: 8c9756b28d64dab099da31a4c09229a9e6a2ef35
phase: wasm
pass: none
discovered-by: invariant-check
first-seen: 2026-07-18
reproduction: Fir/Wasm/Concrete/HeapRefinement.lean
regression: Fir/Wasm/Concrete/ReuseMemoryCorrectness.lean
---

# Summary

Successful in-place reuse may install a smaller active constructor layout
while retaining the old physical allocation extent, but
`ConstructorObjectRel` currently requires those byte counts to be equal.

## Minimal reproduction

Start with a related constructor whose decoded header has allocation size
`oldBytes`. Reset it uniquely, then reuse its nonempty token with constructor
metadata whose `ConstructorLayout.ofInfo` needs `newBytes < oldBytes`.
`reuseObject` accepts the token, erases the complete old payload, installs the
new fields and metadata, and deliberately leaves `header.allocationBytes =
oldBytes` so the spatial allocation boundary remains self-describing.

Reconstructing `ConstructorObjectRel` for the new constructor requires

```text
header.allocationBytes.toNat = (ConstructorLayout.ofInfo newInfo).allocationBytes
```

which reduces to `oldBytes = newBytes` and is false.

## Exact commands

```text
lean-beam sync Fir/Wasm/Concrete/ReuseMemoryCorrectness.lean +full
```

Attempt to construct the target `ConstructorObjectRel` after a successful
reuse whose checked capacity inequality is strict.

## Expected semantics

The refinement relation should distinguish the constructor's active logical
layout from the retained physical allocation capacity. The active layout must
fit inside the decoded capacity; the complete retained extent must remain
below the heap cursor and participate in descriptor disjointness.

## Actual behavior

The concrete runtime and byte-level transaction retain the correct physical
extent, but the normal constructor relation identifies that extent with the
fresh-layout size. Consequently a successful shrinking reuse cannot re-enter
the normal whole-heap relation.

## Proof or differential evidence

`LinearMemory.reuseConstructorMemory_spec` proves that the replacement fields
fit, that every byte outside the retained allocation is framed, and that the
replacement header is published with the retained extent. The remaining
failure is the exact-size clause in `ConstructorObjectRel`, not an executable
memory discrepancy.

## Semantic impact

The W6 reset/reuse proof can cover same-size replacements but cannot justify
the runtime's intentionally supported smaller-layout path. Replacing the
retained size with the smaller logical size would also break spatial framing
by making the physical tail invisible to descriptor disjointness.

## Classification and triage

This is a Wasm refinement-model defect. The repair is to require active-layout
fit (`newBytes ≤ retainedBytes`) while using the decoded retained byte count
for allocation extent and framing. The semantic FIR runtime does not need to
change.

## Workaround

No workaround remains. The constructor relation now separates active-layout
fit from the self-describing retained physical extent.

## Upstream tracking

none

## Resolution and regression

Resolved in W6.3ai by replacing `ConstructorObjectRel`'s exact allocation-size
equation with the checked capacity inequality used by the concrete runtime.
`LiveHeapRel.descriptorRegion` continues to own the complete decoded retained
extent, while `MemoryState.AllocationFrame.shrink` lets proofs recover the
smaller active logical prefix needed for constructor observations.

Constructor allocation, field/scalar mutation, and whole-heap framing were
reproved against the generalized relation. `Fir.Wasm.Concrete.Examples` now
guards a strict shrinking reuse: the active metadata changes from a mixed
56-byte layout to one object field while the header continues to advertise
the retained 56-byte capacity and the replacement field reads back exactly.
