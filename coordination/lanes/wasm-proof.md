# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: bd5e28ab; W7 scratch-free Nat decision generation c96cf72d plus its direct-result ratchet bd5e28ab, stacked over accepted main 3fdbfc6d
functional-head: 18bb219e
contract-base: W7 Nat.decEq/decLt/decLe source c96cf72d and exact-shape/lean-zip ratchet bd5e28ab
clean-at-update: true
slice: Closed operational thread W7-W6-20260820-012 for resident Nat.decEq, Nat.decLt, and Nat.decLe. The exact generated two-local bodies adapt to Talos with the checked arbitrary-precision fallback preserved. Under ImmediateNaturalPairRel, each actual adapted helper selects the immediate comparison, returns the exact normalized UInt8 through the typed i32-to-i64-to-UInt8 roundtrip, and leaves the store and caller tail unchanged. The proof no longer requires positive linear-memory pages or scratch loads, stores, and locals. The existing exact W6 UInt8 value relation remains the result boundary.
files: integration/talos/FirTalos/ConcreteResidentNatDecision.lean; coordination/lanes/wasm-proof.md
contracts: none changed. The proof consumes the W7 public helper bodies and existing semantic ABI, ImmediateNaturalPairRel, typed scalar instruction semantics, and W6 UInt8 value relation. The checked fallback and its validation remain intact and opaque; only the immediate path proof was adapted to the new scratch-free implementation.
checks: Lean Beam update/sync/save passed for ConcreteResidentNatDecision.lean with zero diagnostics and source hash 49832e31c4a4859b. `lake build FirTalos.ConcreteResidentNatDecision` passed (3,079 jobs). `git diff --check` passed. `make talos-setup` passed at Talos 0e05edbc. `make check` passed (713 unique cases, 2,121/2,121 comparisons equal, zero findings, 191 active bug cards, 25 mailbox tests). `make talos-check` passed (3,167 jobs).
bug-cards: none
blockers: none
handoff: Integration should atomically land W7 generation c96cf72d, its ratchet bd5e28ab, W6 functional proof 18bb219e, and this containing tracked-mailbox commit over main 3fdbfc6d. This avoids a Talos-red intermediate main. No W7 implementation, artifact, fixture, profile, shared contract, root umbrella, BOARD file, or bug card was modified by W6.
next: After integration accepts this stack, rebase wasm/talos-runtime on the new main and consume the next W7 proof request from the operational mailbox.
```
