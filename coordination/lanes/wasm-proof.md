# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 5c9449e9 on main
functional-head: 4f96ef0a
contract-base: 181b1097; consume the landed W7 immediate-Nat decision dispatcher at generation head 9dd5ea7a without changing helper signatures, semantic ABI, concrete layout, ownership, or arena contracts
clean-at-update: true
slice: One representation theorem proves that equality and unsigned ordering of canonical tagged immediate words are exactly Nat equality, strict order, and non-strict order. One factored Talos WP theorem covers the eq/lt/le comparison instructions. ConcreteResidentNatDecision proves the exact FIR-to-Talos adaptation shape of all three public Nat decision helpers, preserves the complete checked arbitrary-precision fallback as the same adapted target program, threads both raw-result writes plus the scratch-memory UInt8 cast, and proves fuel-free termination of the actual adapted helper for every canonical immediate pair. The final result is precisely the source semantic UInt8 decision byte, with unchanged store and caller operand tail. The existing pure-scalar external theorem and compiler admission remain unchanged for promoted, heap-backed, mixed-representation, and arbitrary-limb values.
files: Fir/Wasm/Concrete/NaturalDispatchCorrectness.lean; integration/talos/FirTalos/ConcreteResidentPrimitives.lean; integration/talos/FirTalos/ConcreteResidentNatDecision.lean; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none. No W7 generator/artifact file, helper signature, semantic ABI, concrete representation, ownership rule, source semantics, compiler relation, or shared integration-owned file changed.
checks: After rebasing functional head 4f96ef0a on main 5c9449e9, Lean Beam refresh/sync/save for FirTalos/ConcreteResidentNatDecision.lean passes with zero errors or warnings; lake build FirTalos.ConcreteResidentNatDecision passes (3,079 jobs); git diff --check passes; make check passes (163 scalar Wasm exports, 125 unit tests, 704 source cases across native/LCNF/V8, nine direct-machine cases, 2,121/2,121 comparisons equal, 713-case aggregate coverage, zero findings, 190 active bug cards, 25 mailbox tests); make talos-setup passes at Talos 0e05edbc; make talos-check passes (3,162 jobs)
bug-cards: none new
blockers: none for this handoff. The proof-owned module is intentionally not added to integration/talos/FirTalos.lean because that umbrella is integration-owned; integration should add the one-line import while consuming the candidate. Full operation-specific StateRelated replacement remains a later W6 theorem, not a defect in this immediate-helper slice.
handoff: Ready green W6 proof candidate at functional head 4f96ef0a, rebased on main 5c9449e9. Integration may add `import FirTalos.ConcreteResidentNatDecision` to its umbrella, rerun the gates, and land the candidate. This handoff proves all three actual immediate decision helpers and structurally preserves the checked fallback; it does not claim a new resident fallback theorem or the final whole-export replacement instance.
next: After integration, take the queued W7 immediate Nat-to-USize proof adaptation. In parallel, continue operation-specific StateRelated successors and promoted/heap-backed Nat.add toward the generic resident replacement theorem.
```
