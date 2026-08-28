# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 330e6366327748cbf889e5e764da8a7edd84df91
functional-head: 330e6366327748cbf889e5e764da8a7edd84df91
contract-base: 330e6366327748cbf889e5e764da8a7edd84df91
clean-at-update: true
slice: Define retained constructor-schema provenance and its agreement with the active refinement witness, then use the combined source/target relation to discharge object-field admission without a universal witness premise.
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: pending proof-side relational invariant design; no shared semantic contract change intended
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: Active on wasm/talos-runtime; not ready for integration.
next: Audit existing heap/object provenance relations and allocation/reuse transitions before selecting the minimal relational schema.
```
