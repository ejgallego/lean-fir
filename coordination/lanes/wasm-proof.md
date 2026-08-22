# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 713c6e52, current pushed main after the tooling-only integration
functional-head: c0427a57
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Proved the typed checked Nat.add result paths on the exact W7 body. The one-limb branch obtains its canonical object relation from the adapted naturalSum/makeNatural concrete allocation. The multi-limb branch now has exact prefix, count dispatch, allocator/writer, optional carry stores, and typed-return Talos theorems; both carry outcomes close against allocateNatural_heap_liveHeapRel and ResidentMemoryRel, so no arbitrary i32 is admitted as tobject. The common scale-by-eight address calculation and constant half-limb stores are factored as reusable physical-memory lemmas. The generated checked return remains address-zero scratch-free. W6 PLAN records the representation boundary and follow-up induction.
files: integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. Proof-side helper names are explicitly unstable and may be reshaped for a cleaner induction boundary.
checks: Lean Beam update/sync/save passed for FirTalos/ConcreteResidentNat.lean with zero diagnostics. Forced `lake env lean FirTalos/ConcreteResidentNat.lean` passed. Focused `lake build FirTalos.ConcreteResidentNat` passed all 3,118 jobs. Before and after rebase, `git diff --check`, `make check`, `make talos-setup`, and `make talos-check` passed; the final rebased gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,167 Talos jobs.
bug-cards: none
blockers: none for landing this useful typed-result checkpoint
handoff: Integration may fast-forward main from 713c6e52 through the exact W7 commits fcc47335, 3cdb7ce1, 208f8095 and W6 functional head c0427a57, followed by this containing status commit. W7 may use the landed typed-result/carry-store checkpoint immediately.
next: Prove the installed sumCarryFrom and writeSumFrom structured loops with a processed-limb-prefix invariant, show both return the same carry bit and that final memory is allocateNatural of the mathematical operand sum, then compose the already-proved exact prefix and result branches into the full checked Nat.add refinement. This is a semantic implementation proof, not a certificate.
```
