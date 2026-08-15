# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: f3b24d80 on main
functional-head: 1382363d
contract-base: f3b24d80; consume the landed resident Array, immediate-Nat, and complete scalar Wasm surfaces without changing their signatures or shared ABI
clean-at-update: true
slice: W7-W6-20260814-007/008 complete. The shared odd-word dispatcher selects exactly two canonical immediate Nat representations, shift-right decodes their exact payloads, and the complementary branch heap-classifies at least one operand. Nat.add reuses canonical natural allocation, including promoted persistent sums. Nat.mod now has an exact concrete immediate-branch model and refinement theorem: divisor zero returns the original left word; a nonzero remainder is proved below the immediate range, so canonical construction leaves memory and the refinement witness exactly unchanged. The checked arbitrary-precision fallback is unchanged.
files: Fir/Wasm/Concrete/NaturalDispatchCorrectness.lean; Fir/Wasm/Concrete.lean; coordination/lanes/wasm-proof.md
contracts: none. No helper signature, ABI, concrete layout, ownership rule, semantic relation, or W7-owned source changed.
checks: Lean Beam update/sync/save pass for Fir/Wasm/Concrete/NaturalDispatchCorrectness.lean with zero errors or warnings; lake build Fir.Wasm.Concrete.NaturalDispatchCorrectness Fir.Wasm.Concrete pass (62 jobs); git diff --check pass; make check pass (163 scalar Wasm exports, 125 unit tests, 704 source cases across native/LCNF/V8 with 2,112/2,112 comparisons equal, 713-case aggregate coverage, zero findings, 188 active bug cards, 25 mailbox tests); make talos-setup pass at Talos 0e05edbc; make talos-check pass (3,149 jobs)
bug-cards: none
blockers: none for this slice. The separate unchecked typed Array admission gap remains recorded in W7-W6-20260814-004 and does not affect the Nat dispatcher/add/mod theorems.
handoff: Integration may land functional-head 1382363d and its containing ready mailbox commit from wasm/talos-runtime on base f3b24d80.
next: Return to the typed unchecked Array compiler-admission gap, or consume the next dependency-ordered W7 proof request after integration accepts this Nat milestone.
```
