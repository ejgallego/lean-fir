# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 6fbb1da5, tracked prior W6 completed-payload decoder handoff over the accepted W7 checked-Nat contract
functional-head: e46ead82
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Derived the complete W6 NaturalObjectRel from the raw resident allocator/writer boundary. Successful reservation now exposes the common payload nonwrap bound; WrittenLimbPrefix preserves resident page count and every byte of the 32-byte common header, including across the optional carry store. A reusable ResidentMemoryRel theorem transports such a header frame from the allocator store to the final W6 checked readLiveHeader. The final object theorem combines the initial allocator memory relation, exact writer history, final memory relation, unchanged cursor, payload bound, and extensional decoded value into kind, marker, ordinary/refcount metadata, aligned capacity, extent, and readNatural correctness. W7 no longer needs to supply an independent final-header premise or canonical limb-list equality. W6 PLAN records the narrowed live-heap/witness boundary.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. New theorem and proof-side helper names remain explicitly unstable.
checks: Lean Beam sync/save passed for FirTalos/ConcreteResidentNat.lean at source hash 03d47dea215f3888 with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,119 jobs. `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful Natural-object relation checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head e46ead82 and this containing status commit. W7 may rely on initial/final ResidentMemoryRel plus the exact writer history preserving and transporting the allocator header automatically; no additional header certificate, canonical-limb equality, or helper signature change is required.
next: Extend the raw fresh reservation through the refinement witness and spatial live-heap invariants, install the derived NaturalObjectRel as LiveCellRel.natural, and feed the resulting ValueRel into the existing typed-return suffix and whole checked-addition theorem.
```
