# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: f161a37f on main
functional-head: 2557bcbe
contract-base: f161a37f; consumes the accepted structured machine, Talos semantic surface, adapter layout, and current W7 resident-runtime stack
clean-at-update: true
slice: Complete W6.7d structured terminal adequacy. StructuredWasmCompletion assigns exact Talos meaning to every control state and frame stack; one-step and finite-path collapse cover calls, blocks, conditionals, loops, branches, and returns. Successful FirTalos.adapt proves the zero-parameter-loop invariant and automatically discharges path arity safety. StructuredWasmStep.finitePath_run_of_adapt concludes the exact Wasm.run final store and normalized result stack for every sufficiently large fuel.
files: integration/talos/FirTalos/Correctness/StructuredWasmAdequacy.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; proves adequacy for the accepted structured-machine, adapter, and Talos semantic contracts without changing them
checks: Lean Beam update/sync/save FirTalos/Correctness/StructuredWasmAdequacy.lean (green, no errors); lake build FirTalos.Correctness.StructuredWasmAdequacy FirTalos.ConcreteResumableWasm (green before and after rebase); git diff --check main...HEAD (green); make check (green, 642 validation cases and 1844 backend comparisons); make talos-setup (Talos a01d01c); make talos-check (green, 3132 jobs)
bug-cards: none
blockers: none
handoff: ready for integration from wasm/talos-runtime; branch is rebased on f161a37f and clean at this mailbox update
next: W6.7e: define the compiler-derived source/structured-target relation and silence rank, then construct a finite structured path and restore the relation for the first admitted source-step family.
```
