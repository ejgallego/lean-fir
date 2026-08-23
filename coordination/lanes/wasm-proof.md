# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 44ac981a, current main after accepted closed-closure dispatch
functional-head: 434e1fa9
contract-base: 44ac981a; the current W7 checked-Nat body and resident low/high helper signatures are consumed unchanged
clean-at-update: true
slice: Closed the installed natural-flavor magnitude-dispatch chain. `Header.read_aux1_eq_ok` is a reusable projection from a successful checked header decode. The actual adapted `naturalCount` helper is proved for tagged and heap naturals; the heap theorem transports the live header count through `ResidentMemoryRel`. The actual adapted `magnitudeCount` helper delegates flavor zero to that count theorem. The actual adapted `magnitudeLow` and `magnitudeHigh` helpers are then proved in both branches: an index outside the operand count returns zero without a limb call, while an in-range index delegates to the previously proved arbitrary-index natural accessor. These theorems preserve the exact store and caller tail and assume no integer-helper behavior.
files: Fir/Wasm/Concrete/HeaderCorrectness.lean; integration/talos/FirTalos/ConcreteResidentBigNumeric.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: Current main/W7 generation contracts are consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, resident helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. `Header.read_aux1_eq_ok` and the count/magnitude execution theorems are proof-side W6 surfaces and explicitly unstable.
checks: Lean Beam update/sync/save passed with zero diagnostics for HeaderCorrectness.lean (source hash f7a3034ae2b3365c) and ConcreteResidentBigNumeric.lean (33a4a40c69111336). Focused `lake build FirTalos.ConcreteResidentBigNumeric` passed all 3,073 jobs. Final `git diff --check`, `make check`, `make talos-setup`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 192 active bug cards, 25 mailbox tests, and all 3,171 Talos jobs. Talos is pinned at 0e05edbc.
bug-cards: none new; FIR-BUG-wasm-none-frontier-word-modulus-boundary remains the separately coordinated raw-allocator endpoint contract issue
blockers: none for landing this useful dispatcher checkpoint; the checked Nat.add producer now has a frame/composition obligation rather than an unproved helper-code obligation
handoff: Integration may fast-forward the accepted stack through W6 functional head 434e1fa9 and this containing status commit. W7 may rely on installed natural-flavor count and magnitude low/high calls, including exact zero padding outside an operand's own count, rather than supplying trusted dispatcher `TerminatesWith` premises.
next: Prove that writes into the fresh Nat.add result preserve both input natural views and the W6/Talos memory relation, use that frame to instantiate the four evolving-store magnitude calls required by `terminatesWith_writeSumFromFunction_of_exactPrefix`, then compose allocator, writer, and typed live-heap closure.
```
