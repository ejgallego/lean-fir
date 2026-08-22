# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 28ea02df, tracked prior W6 resident raw-allocator refinement handoff
functional-head: c95485d2
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Factored resident writer proofs around reusable abstractions and closed the BigNumeric common-header boundary. ResidentMemoryRel now provides compact store updates, a generic adjacent-word fold with exact store equality, and compositional WP rules for prepared, local, constant, constant-plus-local stores and local return. ResidentAllocatorRel.writeUInt32s and writeHeader lift any checked W6 word/header write through the complete allocator relation. ConcreteResidentBigNumericAllocator identifies the exact W7 source and Talos bodies, proves adaptation, proves scalar execution of the count guard, scale-by-eight calculation, raw allocator call, all eight checked header stores and returned address, and connects its compact physical writer to generic W6 Header.write refinement, including the canonical nonpersistent allocation header.
files: integration/talos/FirTalos/ConcreteResidentMemory.lean; integration/talos/FirTalos/ConcreteResidentAllocator.lean; integration/talos/FirTalos/ConcreteResidentBigNumericAllocator.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. The compact store operations, generic writer lemmas, and BigNumeric execution/refinement theorems are proof-side W6 surfaces and explicitly unstable.
checks: Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentMemory.lean (source hash cb50186a1262fe42), ConcreteResidentAllocator.lean (5cc06c2c36935d62), ConcreteResidentBigNumericAllocator.lean (3c34e290a1358028), and ConcreteResidentNat.lean (6af706a3809acac9). Focused `lake build FirTalos.ConcreteResidentMemory FirTalos.ConcreteResidentAllocator FirTalos.ConcreteResidentBigNumericAllocator` passed all 3,065 jobs. Final `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 192 active bug cards, 25 mailbox tests, and all 3,170 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none new; FIR-BUG-wasm-none-frontier-word-modulus-boundary remains the separately coordinated raw-allocator endpoint contract issue
blockers: none for landing this useful header-execution checkpoint; the full object allocator theorem still needs the existing raw allocator theorem instantiated at the abstract call boundary
handoff: Integration may fast-forward the accepted stack through W6 functional head c95485d2 and this containing status commit. W7 may reuse the generic store/WP surface for resident object writers and rely on wp_allocateObjectProgram for the exact emitted BigNumeric allocation body once its raw allocator call supplies the stated TerminatesWith result. The matching-header refinement theorem then transports the physical writer result into the complete W6 ResidentAllocatorRel.
next: Instantiate wp_allocateObjectProgram's raw call with wp_allocateProgram_of_allocate and package the complete W6 allocateObject transition; then compose the already-proved writeSumFrom execution and self-contained live-heap/typed-return closure before attaching the checked Nat.add dispatcher.
```
