# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: b13710cd on main
functional-head: cb04d7ee (landed on main through f37af09e)
contract-base: b13710cd; consume the landed resident Array and immediate-Nat helper implementations without changing their signatures or shared ABI
clean-at-update: true
slice: Active W6/W7 bridge milestone. First audit the trusted resident Array header and proof-indexed unchecked-bounds premises requested by W7-W6-20260814-001/004. Then adapt the W6 refinement to the landed reusable immediate-Nat dispatcher used by Nat.add and Nat.mod in W7-W6-20260814-007/008.
files: coordination/lanes/wasm-proof.md initially; W6-owned concrete/runtime proof files after the audits identify the smallest Nat refinement surface
contracts: none planned. The accepted W7 Array and Nat helper implementations retain the existing semantic ABI, concrete layout, ownership model, and helper signatures.
checks: not-run for this active milestone
bug-cards: none yet
blockers: none; W7-W6-20260814-004 follows the W7-W6-20260814-001 Array audit, and W7-W6-20260814-008 follows the W7-W6-20260814-007 Nat-add adaptation.
handoff: none; milestone active on current main b13710cd
next: Acknowledge all four operational threads, complete the dependency-ordered Array audits, implement the shared immediate-Nat dispatch/add/remainder proof, run the W6 dependency cone and full required gates, and stop at a clean checkpoint.
```
