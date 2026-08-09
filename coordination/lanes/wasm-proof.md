# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: b1aa9a95 on main
functional-head: none yet
contract-base: b1aa9a95 on main; ranked finite-trace and instruction-boundary adequacy milestones are linked/accepted; no shared semantic or runtime contract is queued
clean-at-update: true
slice: Inventory the compiler-emitted structured instruction subset; reify the necessary call, block, conditional, and loop frames into a target small-step configuration that exposes internal progress; prove finite terminal paths collapse to the checked instruction-boundary/Talos adequacy theorem
files: coordination/lanes/wasm-proof.md; anticipated proof-owned additions under integration/talos/FirTalos/Correctness/ and integration/talos/FirTalos/
contracts: none anticipated; this slice should add a proof-local semantics and adequacy layer without changing the shared symbolic Wasm instruction surface, Talos, concrete layout/runtime, resident helpers, or artifacts
checks: pending; Lean edits will use Lean Beam, followed by focused/umbrella builds, git diff --check, make check, make talos-setup, and make talos-check
bug-cards: none
blockers: none
handoff: none; active slice
next: Derive the smallest structured-frame grammar from Fir.Wasm.Lower and the adapter, then implement one frame family at a time with a Talos collapse lemma
```
