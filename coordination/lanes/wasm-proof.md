# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: f3b24d80 on main
functional-head: 71384ff8
contract-base: f3b24d80; consume the landed resident Array, immediate-Nat, and complete scalar Wasm surfaces without changing their signatures or shared ABI
clean-at-update: true
slice: W7-W6-20260814-007 complete. Proved that the shared odd-word dispatcher selects exactly two canonical immediate Nat representations, that shift-right decodes their exact payloads, and that the complementary branch heap-classifies at least one operand. Proved the Nat.add fast branch through the existing canonical natural allocator, including witness extension and the promoted persistent result when the sum exceeds the immediate range; the semantic heap and arbitrary-precision fallback contract are unchanged.
files: Fir/Wasm/Concrete/NaturalDispatchCorrectness.lean; Fir/Wasm/Concrete.lean; coordination/lanes/wasm-proof.md
contracts: none. No helper signature, ABI, concrete layout, ownership rule, semantic relation, or W7-owned source changed.
checks: Lean Beam update/sync/save pass for Fir/Wasm/Concrete/NaturalDispatchCorrectness.lean and Fir/Wasm/Concrete.lean; lake build Fir.Wasm.Concrete.NaturalDispatchCorrectness Fir.Wasm.Concrete pass (62 jobs); git diff --check main...HEAD pass; make check pass after rebase (163 scalar Wasm exports, 125 unit tests, 704 source cases across native/LCNF/V8 with 2,112/2,112 comparisons equal, 713-case aggregate coverage, zero findings, 188 active bug cards, 25 mailbox tests); make talos-setup pass at Talos 0e05edbc; make talos-check pass after rebase (3,149 jobs)
bug-cards: none
blockers: none for this slice. The separate unchecked typed Array admission gap remains recorded in W7-W6-20260814-004 and does not affect the Nat dispatcher/add theorem.
handoff: Integration may land functional-head 71384ff8 and its containing ready mailbox commit from wasm/talos-runtime on base f3b24d80.
next: Complete W7-W6-20260814-008 by reusing the dispatcher for Nat.mod, including the immediate divisor-zero behavior and the unchanged arbitrary-precision fallback.
```
