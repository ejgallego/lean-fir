# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 5429510c on main
functional-head: 2557bcbe (previous accepted slice; no W6.7e functional commit yet)
contract-base: 5429510c; consumes accepted W6.7d terminal adequacy, generated structured machine, concrete runtime refinements, and current W7 resident-runtime stack
clean-at-update: true
slice: Begin W6.7e compiler relation and silence rank. Define the compiler-derived source/structured-target relation spine from existing environment, heap, ownership, continuation, world, and trace refinements; derive observation agreement; then construct and restore the relation for the smallest admitted source-step family with an explicit finite structured target path and zero-step rank decrease.
files: coordination/lanes/wasm-proof.md; intended proof-owned modules under integration/talos/FirTalos/
contracts: none; this slice constructs the simulation over accepted source, structured-target, and concrete-runtime contracts
checks: not-run
bug-cards: none
blockers: none
handoff: none; active proof slice
next: Inventory existing direct compiler-state relations and select the first relation-preserving source-step family without weakening admission or adding target execution evidence.
```
