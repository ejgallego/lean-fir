# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 638e05a2c00c8c5056ec67c4bb7fa73d8a16ff96
functional-head: 2380ade5bd5701770266086e7e081deeae31d3cc
contract-base: 638e05a2c00c8c5056ec67c4bb7fa73d8a16ff96
clean-at-update: true
slice: Define the minimal preserved final-LCNF semantic invariant that discharges the sole remaining compiler source-safety field. First classify every source-safety constructor, then prove one coherent constructor family and connect it to the validated global simulation without target paths or future execution evidence.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: none expected; proof-side source semantic invariant only
checks: not-run
bug-cards: none
blockers: none
handoff: none
next: Audit existing phase/runtime invariants and prove the first source-safety extraction family.
```
