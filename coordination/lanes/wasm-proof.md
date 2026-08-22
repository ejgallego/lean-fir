# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 42536f6f, tracked prior W6 exact writer-prefix handoff over the accepted W7 checked-Nat contract
functional-head: 4f91e165
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Projected the exact writeSumFrom materialization history to exact final-memory reads. ConcreteResidentMemory now proves that a Talos write32 preserves every byte and read32 in a disjoint four-byte lane. WrittenLimbAddressesDisjoint records pairwise separation in the unbounded UInt32.toNat address view, making modular nonwrap explicit. WrittenLimbPrefix.readable inductively proves that every pure low/high output word can be read exactly from the final store. W6 PLAN records the resulting allocator-boundary lesson and the next Natural decoding step.
files: integration/talos/FirTalos/ConcreteResidentMemory.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout, runtime/helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. New theorem and proof-side helper names are explicitly unstable and may be reshaped when allocation bounds discharge the separation premise.
checks: Lean Beam update/sync/save passed for FirTalos/ConcreteResidentMemory.lean and FirTalos/ConcreteResidentNat.lean with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentMemory FirTalos.ConcreteResidentNat` passed all 3,119 jobs without warnings. `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests, and all 3,168 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none
blockers: none for landing this useful exact writer-read projection checkpoint
handoff: Integration may fast-forward the accepted stack through W6 functional head 4f91e165 and this containing status commit. W7 may rely on exact pure-output writer materialization and its disjoint-lane read projection without changing writeSumFrom's helper body, local layout, magnitude-accessor behavior, or signature.
next: Derive WrittenLimbAddressesDisjoint from the successful Natural allocation bounds, then connect the decoded completed payload and returned carry to allocateNatural of the operand sum and the existing checked typed-return paths.
```
