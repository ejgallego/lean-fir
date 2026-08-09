# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 56d1c09c on main
functional-head: dbecabba
contract-base: 56d1c09c on main; ranked finite-trace, instruction-boundary adequacy, and emitted frame-collapse laws are linked/accepted; no shared semantic or runtime contract is queued
clean-at-update: true
slice: Defined the explicit emitted-subset frame-stack state and small-step relation with running/breaking/returning/halted control; delegated atomic instructions and imports to Talos; exposed internal call and structured entry, normal label/loop/call exits, loop restart, outward branch propagation, return unwinding, and top-level halting; switched the concrete generated trace-simulation target to this store-exposing structured machine
files: integration/talos/FirTalos/Correctness/StructuredWasmMachine.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/FirTalos.lean; integration/talos/PLAN.md; integration/talos/README.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; adds proof-local target semantics without changing source semantics, symbolic Wasm instructions, Talos, concrete runtime layout/operations, resident helpers, or artifacts
checks: Lean Beam save FirTalos.Correctness.StructuredWasmMachine passed with 0 errors and 0 warnings (source dc84876ba1bae852); Lean Beam save FirTalos.ConcreteResumableWasm passed with 0 errors and 0 warnings (source e1119f9bb10c8f65); lake build FirTalos.Correctness.StructuredWasmMachine FirTalos.ConcreteResumableWasm FirTalos passed (3131 jobs); git diff --check passed; make check passed on the unchanged 642-case/1844-comparison corpus; Talos setup remains pinned at a01d01c778b794dd00956748a067b6793c2c9f9b; make talos-check passed (3131 jobs)
bug-cards: none
blockers: none
handoff: Land functional-head dbecabba plus this ready mailbox; the concrete ranked-simulation alias now uses the structured target, while terminal adequacy remains explicitly a theorem to prove rather than a premise
next: Prove that every finite structured path from a canonical function entry to a halted empty-frame state yields the exact successful Talos run above a finite fuel bound; then instantiate compiler relation/rank cases
```
