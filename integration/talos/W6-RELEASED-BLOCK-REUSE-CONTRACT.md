# W6 released-block reuse contract

Status: initial generic concrete contract proved; production attachment waits
for the W7 generation-ready implementation and the dead-mapping retirement
admission described below.

Bug card: `FIR-BUG-wasm-none-resident-arena-released-block-reuse`.

## Purpose

The resident allocator may satisfy an aligned allocation from an exact-size
canonically released block before advancing the wasm32 frontier.  The W6 model
does not prescribe segregated heads, link placement, or search order beyond
first-match behavior in its abstract sequence.  Those details remain private
to W7 and are related to the abstract index only in the implementation proof.

The proof-facing model is
`Fir.Wasm.Concrete.ReleasedBlockReuseCorrectness`.

## Minimal W7 source-shape facts

W7 should expose the following facts about the generated helpers.  No concrete
free-list representation is part of the shared semantic contract.

1. **Offer after canonical release.** An entry is linked only after the full
   `Header.forRelease` store has completed on an ordinary last-reference or
   explicit-delete path.  Its recorded extent is the retained
   `allocationBytes` word.  Shared and persistent objects do not reach this
   path.
2. **Exact selection and unique unlink.** A successful reuse branch returns
   one entry whose extent equals the aligned request and removes that entry
   before returning.  The remaining abstract entries stay valid, unique, and
   pairwise disjoint.  A different size is skipped; no match takes the existing
   bump/grow path exactly.
3. **Allocator-private metadata.** List heads and links are not decoded as live
   Lean objects.  A link may occupy ignored payload bytes of a canonical dead
   allocation, but not the common released-header words frozen by
   `DeadCellRel`.  A stale decrement must continue to fail at the dead header.
4. **Initialize before exposure.** After unlinking, the caller writes the
   complete new live header and every logically readable kind-specific payload
   component before the address becomes a source-visible value.  Raw reuse
   does not promise a zero payload.
5. **Rewind invalidation.** `fir_heap_rewind` clears the complete reuse index or
   retains only entries whose complete extents lie below the restored
   checkpoint.  The persistent-cache floor is applied before this test.  No
   entry at or above the effective checkpoint survives.
6. **Unchanged fallback and ABI.** The no-match branch is the existing checked
   allocator, including alignment, memory growth, and wasm32 overflow checks.
   The zero sentinel, tagged values, recursive release order, cache floor,
   host-resource ownership, and public application ABI are unchanged.

These facts are sufficient for W6 even if W7 uses a bounded segregated table
below `heapBase`, clears all heads on rewind, or later changes its private link
encoding.

## Proved theorem surface

| Boundary | Theorem or definition |
| --- | --- |
| Canonical indexed block | `ReleasedBlock.Valid` |
| Release-to-index bridge | `MemoryState.FrontierInvariant.releaseHeader_reusable` |
| Exact first-match removal | `ReleasedBlockIndex.takeExact_sound` and `TakesExact.*` |
| Valid remainder | `ReleasedBlockIndex.TakesExact.remainingValid` |
| Rewind filtering | `ReleasedBlockIndex.Valid.invalidateForRewind` |
| Weaker post-rewind frontier facts | `MemoryState.AllocatorInvariant` |
| Reuse-or-bump allocator model | `MemoryState.allocateReusing` |
| Complete branch classifier | `MemoryState.allocateReusing_spec` |
| Dead/exact/removed result | `MemoryState.ReusableAllocatePost.reusedFacts` |
| Index and frontier preservation | `ReusableAllocatePost.remainingValid` and `.allocatorInvariant` |
| Existing finite budget compatibility | `ReusableAllocatePost.addressSpaceBudget` |
| Fresh header ownership restoration | `ReleasedBlock.Valid.initializeReleasedBlock` |

The allocator-level invariant is intentionally weaker than
`MemoryState.FrontierInvariant`: rewinding does not zero the old scratch suffix.
Consequently, a post-rewind or reused allocation must be fully initialized by
its resident producer before exposure.  Existing monotone fresh-allocation
proofs may continue to use the stronger zero-suffix invariant.

## Whole-simulation admission still required

`LiveHeapRel` currently remembers a dead semantic location at its released
physical address.  `RefinementWitness.WellFormed` also makes the location map
injective.  Therefore the same witness cannot bind that address to a distinct
new semantic location; this is formalized by
`RefinementWitness.WellFormed.reusedAddress_requires_sameLocation`.

This is a soundness boundary, not a free-list implementation detail.  Without
an unreachability fact, a stale source reference would still fault on the dead
location while the same target word could name the newly live object.

Production attachment must therefore prove one of these equivalent policies:

- compiler/runtime ownership proves the released location unreachable, after
  which the witness may retire its dead mapping before rebinding; or
- the heap relation becomes generation-aware and distinguishes the retired
  address generation from the new one.

The first policy is the smaller next step and matches Lean ownership.  The
target theorem should retire only a canonical dead, zero-reference location
that is absent from source environments, globals, live owned fields, suspended
frames, and foreign roots.  It must not weaken the public stale-reference
fault theorem for arbitrary states.

## Production attachment order

1. W7 publishes a clean helper/source-shape checkpoint satisfying the six
   facts above.
2. W6 proves the generated release, selection, unlink, initialization, rewind,
   and bump branches refine this abstract model.
3. W6 adds the unreachable-dead-mapping retirement lemma at the structured
   runtime relation, then composes allocation with witness rebinding.
4. Integration enables production attachment and runs the complete Talos,
   artifact, VBP, and differential gates.
