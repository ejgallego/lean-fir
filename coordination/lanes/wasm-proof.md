# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 44ac981a, current main after accepted closed-closure dispatch
functional-head: aea5afc5
contract-base: 44ac981a; the current W7 checked-Nat body and resident low/high helper signatures are consumed unchanged
clean-at-update: true
slice: Closed arbitrary-index resident Natural magnitude access. `ResidentPrimitives` now owns the exact three-doubling source/Talos spelling, modular `scale8Word`, and reusable weakest-precondition theorem shared by readers and writers. The Nat-local writer API remains source-compatible but delegates to that common proof. The BigNumeric accessor module is now Nat/USize-independent and included in the normal Talos dependency cone. `terminatesWith_naturalLimb_of_adapted` proves either installed low/high helper at any checked physical index, and `terminatesWith_naturalLimb_of_concreteRead` transports an exact W6 finite-memory read while one payload bound discharges both access safety and wasm32 non-wrapping. `ReadableLimbPrefix.naturalLimbCalls` packages any in-prefix writer word pair into exact low/high calls with unchanged store and caller tail. The zero-index USize packaging theorem moved above the accessor layer without changing its public name or result.
files: integration/talos/FirTalos/ConcreteResidentPrimitives.lean; integration/talos/FirTalos/ConcreteResidentBigNumeric.lean; integration/talos/FirTalos/ConcreteResidentNat.lean; integration/talos/FirTalos/ConcreteResidentUSize.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: Current main/W7 generation contracts are consumed unchanged. No source semantics, semantic ABI, concrete layout/runtime definition, resident helper signature, symbolic Wasm surface, ownership behavior, or emitter changed. The new shared scale-by-eight primitive and arbitrary-index accessor/refinement theorems are proof-side W6 surfaces and explicitly unstable.
checks: Lean Beam update/sync/save passed with zero diagnostics for ConcreteResidentPrimitives.lean (source hash d359a1848f7abb75), ConcreteResidentBigNumeric.lean (0a0ed2ddf9617d47), ConcreteResidentNat.lean (16ab5c54a1d684d6), and ConcreteResidentUSize.lean (6b98c90aba26b23b). Before the final rebase, focused `lake build FirTalos.ConcreteResidentUSize` passed all 3,124 jobs and forced the complete modified dependency cone. Functional commit aea5afc5 then rebased cleanly onto main 44ac981a. Final `git diff --check`, `make check`, `make talos-setup`, and `make talos-check` passed; the full gate has 713 unique validation cases, 2,121/2,121 comparisons equal, zero findings, 192 active bug cards, 25 mailbox tests, and all 3,171 Talos jobs. Talos is pinned at 0e05edbc.
bug-cards: none new; FIR-BUG-wasm-none-frontier-word-modulus-boundary remains the separately coordinated raw-allocator endpoint contract issue
blockers: none for landing this useful accessor checkpoint; the checked Nat.add producer still needs to instantiate these operand calls and compose the already-proved allocator and writer calls
handoff: Integration may fast-forward the accepted stack through W6 functional head aea5afc5 and this containing status commit. W7 may now rely on arbitrary-index installed low/high calls derived from a concrete resident-memory read or directly from `ReadableLimbPrefix`, rather than supplying trusted accessor `TerminatesWith` premises.
next: Instantiate `ReadableLimbPrefix.naturalLimbCalls` for both checked Nat.add operands, compose the actual BigNumeric allocator and `writeSumFrom` calls, and feed the resulting exact prefix to the existing self-contained live-heap/typed-return closure.
```
