# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 53349ea2, tracked prior W6 self-contained resident-Natural heap-construction handoff
functional-head: d3999657
contract-base: fcc47335, the rebased exact W7 checked-Nat typed-return body; the following W7 ratchet and coordination commits are consumed unchanged
clean-at-update: true
slice: Proved the actual emitted resident raw allocator refines W6 MemoryState.allocate. ResidentAllocatorRel now records exact in-bounds bytes, the resident frontier global, heap-base and strict wasm32 cursor bounds, plus zero bytes beyond Talos's visible extent so memory.grow matches W6 growToFit. Exact WP theorems cover no-growth and successful-growth execution, and wp_allocateProgram_of_allocate derives every machine check, exact old-frontier return, final pages, frontier update, and successor relation from a successful aligned W6 allocation and module capacity. The symbolic W7 body adapts exactly to the proved Talos program. The proof exposed the exact-2^32 endpoint mismatch rather than weakening the relation.
files: integration/talos/FirTalos/ConcreteResidentAllocator.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; bugs/FIR-BUG-wasm-none-frontier-word-modulus-boundary.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: W7 generation contract fcc47335 is consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. ResidentAllocatorRel and the new execution theorems are proof-side W6 surfaces and explicitly unstable. A future strict allocation-end repair is a shared W6 contract change and is not included in this handoff.
checks: Lean Beam sync/save passed for FirTalos/ConcreteResidentAllocator.lean at source hash a28cfd369fc41ed2 with zero diagnostics. Focused `lake build FirTalos.ConcreteResidentAllocator FirTalos.ConcreteResidentNat` passed all 3,120 jobs. `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 192 active bug cards, 25 mailbox tests, and all 3,169 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: FIR-BUG-wasm-none-frontier-word-modulus-boundary (candidate): W6 admits successor cursor 2^32 while the i32 resident frontier necessarily rejects/wraps it
blockers: none for landing this useful allocator-execution checkpoint; unconditional allocator refinement awaits the separately coordinated strict-end contract repair
handoff: Integration may fast-forward the accepted stack through W6 functional head d3999657 and this containing status commit. W7 may rely on wp_allocateProgram_of_allocate for exact execution of fir_heap_alloc in both memory branches, provided its caller supplies the explicit strict endpoint and module-capacity premises. The theorem returns a store satisfying the complete allocator relation and the original W6 heap address.
next: Prove the BigNumeric object allocator's eight common-header stores realize the W6 allocateObject header transition on top of wp_allocateProgram_of_allocate; then attach the actual writeSumFrom call so its WrittenLimbPrefix feeds the existing self-contained live-heap/typed-return closure and checked Nat.add dispatcher.
```
