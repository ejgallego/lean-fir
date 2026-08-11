# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 5429510c on main
functional-head: e05013ab
contract-base: 5429510c; consumes accepted W6.7d terminal adequacy, generated structured machine, concrete runtime refinements, and current W7 resident-runtime stack
clean-at-update: true
slice: W6.7e compiler-relation first vertical slice. ConcreteStructuredCodeFocus ties one source code focus to the actual two-stage adapted structured-Wasm program, exact target control/locals/store, and the existing concrete StateRelated runtime relation. Observation agreement is derived from that relation. compilerCodeSilenceDepth/rank counts leading erased persistent ownership operations, and the incPersistent/decPersistent preservation theorems take one real source step, use a zero-length target FinitePath, restore the same compiler focus, and strictly decrease the rank.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/W6-THEOREM-ROADMAP.md; coordination/lanes/wasm-proof.md
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: Lean Beam update/sync/save (0 errors, 0 warnings); lake build FirTalos.ConcreteStructuredSimulation FirTalos.ConcreteResumableWasm (3,107 jobs); git diff --check; make check (642 unique cases, 1,844/1,844 backend comparisons, 124 bug cards, trusted assumptions green); make talos-setup (Talos a01d01c); make talos-check (3,133 jobs)
bug-cards: none
blockers: none
handoff: ready for fast-forward integration by the wasm-proof integration owner
next: Add the first positive target-path case: source return through adapted local.get/result and structured ret, with an explicit yielded/returning compiler relation.
```
