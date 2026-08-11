# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: be7eb514 on main
functional-head: db09c2ef (unified structured compiler control relation and observation law; already integrated)
contract-base: be7eb514; proof work over the accepted structured compiler/runtime contracts; intervening capture-topology fixtures change no W6 contract
clean-at-update: false
slice: Reopened to split pure external lets at individual source-step boundaries. The current target is an external-call-ready focus reached after compiled argument evaluation, its exact observation law, and integration into ConcreteStructuredControlRel; call/resume and result-binding stages follow without weakening the eventual ranked theorem.
files: coordination/lanes/wasm-proof.md; planned integration/talos/FirTalos/ConcreteStructuredSimulation.lean and W6 roadmap documents
contracts: none planned; proof staging relation only
checks: not-run
bug-cards: none
blockers: none
handoff: none
next: Prove the external argument-staging transition and observation boundary, then extend through imported-call resume and result binding before the saturated-closure pre-entry stage.
```
