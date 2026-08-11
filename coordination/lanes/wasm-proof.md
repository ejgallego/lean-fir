# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 230d805a on main
functional-head: e05013ab (previous accepted slice; no return-path functional commit yet)
contract-base: 230d805a; consumes accepted W6.7d terminal adequacy, the accepted W6.7e compiler-focus/silence spine, generated structured machine, concrete runtime refinements, and current W7 resident-runtime stack
clean-at-update: true
slice: Continue W6.7e with the first positive structured target path. Define the yielded/returning relation needed at a function boundary, invert successful adaptation of source return, resolve the source result through StateRelated, execute generated local.get and structured ret, and prove that one source return step is matched by the explicit finite target path while preserving concrete observations.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: not-run
bug-cards: none
blockers: none
handoff: none; active proof slice
next: Inspect return adaptation, StateRelated.resolve, and structured local.get/ret step constructors; then prove the explicit two-step path without adding an execution premise to the compiler relation.
```
