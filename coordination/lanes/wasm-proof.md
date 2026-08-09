# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: b1aa9a95 on main
functional-head: 0f466b9c
contract-base: b1aa9a95 on main; ranked finite-trace and instruction-boundary adequacy milestones are linked/accepted; no shared semantic or runtime contract is queued
clean-at-update: true
slice: Inventoried the adapter's emitted structured grammar and proved the first local frame-collapse layer: finite internal calls ending at generated .ret reconstruct exact caller transitions; block fallthrough and br 0, loop fallthrough, and either selected conditional body reconstruct their exact outer Talos instruction-boundary step; added generic finite-prefix break/br adequacy needed for outward propagation
files: integration/talos/FirTalos/Correctness/ResumableWasm.lean; integration/talos/FirTalos/Correctness/StructuredWasmFrames.lean; integration/talos/FirTalos.lean; integration/talos/PLAN.md; integration/talos/README.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; adds proof-local frame equations without changing source semantics, symbolic Wasm instructions, Talos, concrete runtime layout/operations, resident helpers, or artifacts
checks: Lean Beam save FirTalos.Correctness.ResumableWasm passed with 0 errors and 0 warnings (source b33f748a633b7196); Lean Beam save FirTalos.Correctness.StructuredWasmFrames passed with 0 errors and 0 warnings (source 9c26c8bc2b8cb53d); lake build FirTalos.Correctness.ResumableWasm FirTalos.Correctness.StructuredWasmFrames FirTalos.ConcreteResumableWasm FirTalos passed (3130 jobs); git diff --check passed; make check passed on the unchanged 642-case/1844-comparison corpus; Talos setup remains pinned at a01d01c778b794dd00956748a067b6793c2c9f9b; make talos-check passed (3130 jobs)
bug-cards: none
blockers: none
handoff: Land functional-head 0f466b9c plus this ready mailbox; each new theorem reconstructs Talos behavior from target finite paths and adds no caller correctness certificate
next: Define the explicit emitted-subset frame stack and small-step relation, using the checked local laws for completed frames; add loop restart and outward branch propagation before the compiler relation/rank instantiation
```
