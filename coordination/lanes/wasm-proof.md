# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 56406a31, current main after accepted W7 generation and tooling coordination
functional-head: d12fc1b3
contract-base: 56406a31; the current W7 checked-Nat body and resident helper signatures are consumed unchanged
clean-at-update: true
slice: Closed the actual-call boundary for the resident raw allocator, BigNumeric object allocator, and `writeSumFrom`. Canonical target-function descriptions recover complete parameters, locals, results, bodies, and adapter terminal suffixes. `terminatesWith_allocateFunction_of_allocate` derives the installed raw helper call from a successful checked W6 allocation. `wp_allocateObjectProgram_of_allocateObject` and `terminatesWith_allocateObjectFunction_of_allocateObject` compose that call with the count guard and eight header writes, returning a store related to the fully initialized W6 object. `terminatesWith_writeSumFromFunction_of_exactPrefix` lifts the exact structured writer loop through actual adaptation and installation, preserves arbitrary caller tails, and returns both the pure carry and exact `WrittenLimbPrefix` store relation.
files: integration/talos/FirTalos/ConcreteResidentAllocator.lean; integration/talos/FirTalos/ConcreteResidentBigNumericAllocator.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: Current main/W7 generation contracts are consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. The canonical target descriptions and call/refinement theorems are proof-side W6 surfaces and explicitly unstable.
checks: Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentAllocator.lean (source hash 650e6cbb446197e7), ConcreteResidentBigNumericAllocator.lean (9f4979a3b4deb26f), and ConcreteResidentNat.lean (324f2e9b029c8c10). After rebasing onto main 56406a31, focused `lake build FirTalos.ConcreteResidentAllocator FirTalos.ConcreteResidentBigNumericAllocator FirTalos.ConcreteResidentNat` passed all 3,121 jobs. Final `git diff --check`, `make check`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 192 active bug cards, 25 mailbox tests, and all 3,170 Talos jobs. The existing Talos setup remains 0e05edbc.
bug-cards: none new; FIR-BUG-wasm-none-frontier-word-modulus-boundary remains the separately coordinated raw-allocator endpoint contract issue
blockers: none for landing this useful actual-call checkpoint; arbitrary-index magnitude accessor calls remain the next local proof obligation before the writer theorem can be instantiated in the checked Nat.add producer
handoff: Integration may fast-forward the accepted stack through W6 functional head d12fc1b3 and this containing status commit. W7 may rely on the actual installed allocator and writer call theorems rather than supplying trusted `TerminatesWith` premises; the writer theorem returns the exact physical history expected by the existing self-contained heap/typed-return closure.
next: Prove low/high magnitude accessors at arbitrary in-range limb indices from the resident memory relation, then instantiate the allocator/writer calls in the checked Nat.add producer and feed the resulting exact prefix to the existing live-heap/typed-return closure.
```
