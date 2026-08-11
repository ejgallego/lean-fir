# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 3e362ba0 on main
functional-head: ab58cd2e (previous accepted slice; no frame-relation functional commit yet)
contract-base: 3e362ba0; consumes accepted W6.7d terminal adequacy and the accepted W6.7e compiler-focus, silent-ownership, and positive return-path slices over the generated structured machine and concrete runtime refinements
clean-at-update: true
slice: Continue W6.7e with source/target continuation correspondence. Inventory source bind/apply/cache frames and structured target call/label/loop frames, define the smallest compositional frame relation needed around the accepted code/yield focuses, and prove its first restoration/unwinding law without weakening the compiler or runtime relations.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: not-run
bug-cards: none
blockers: none
handoff: none; active proof slice
next: Inventory existing frame-level compiler facts, then select the first frame constructor whose source resume and structured target unwind can be related by current proven runtime laws.
```
