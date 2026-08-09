# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: b4b33102 on main
functional-head: defe31ea
contract-base: b4b33102 on main; ranked finite-trace simulation boundary is linked/accepted; no shared semantic or runtime contract is queued
clean-at-update: true
slice: Added the first concrete target for ranked trace simulation: a resumable outer-instruction state retaining Talos store, locals, and residual program; proved every finite path agrees above one common fuel bound with residual Talos exec; proved exact successful Wasm.run adequacy for fallthrough, general return, and the compiler-emitted .ret exit; packaged the machine with the concrete W6 host and documented the remaining atomic-call/control limitation
files: integration/talos/FirTalos/Correctness/ResumableWasm.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/FirTalos.lean; integration/talos/PLAN.md; integration/talos/README.md; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; adds proof-local target semantics and adequacy theorems without changing source semantics, symbolic Wasm instructions, Talos, concrete runtime layout/operations, resident helpers, or artifacts
checks: Lean Beam save FirTalos.Correctness.ResumableWasm passed with 0 errors and 0 warnings (source 4645a42115a56d27); Lean Beam save FirTalos.ConcreteResumableWasm passed with 0 errors and 0 warnings (source 9227ecaf4ba02e79); lake build FirTalos.Correctness.ResumableWasm FirTalos.ConcreteResumableWasm FirTalos passed (3129 jobs); git diff --check passed; make check passed on the unchanged 642-case/1844-comparison corpus; make talos-setup passed at Talos a01d01c778b794dd00956748a067b6793c2c9f9b; make talos-check passed (3129 jobs)
bug-cards: none
blockers: none
handoff: Land functional-head defe31ea plus this ready mailbox; the target is faithful and adequate at outer instruction boundaries and does not claim internal progress for an atomic call, block, or loop
next: Reify the emitted subset's call and structured-control frames, prove finite terminal collapse to the checked instruction-boundary/Talos theorem, then instantiate compiler relation/rank cases from W6 operation laws
```
