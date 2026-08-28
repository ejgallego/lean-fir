# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 132c8bac5a3d355581f432ba9c9d2e50a0ffd85c
functional-head: 132c8bac5a3d355581f432ba9c9d2e50a0ffd85c
contract-base: 132c8bac5a3d355581f432ba9c9d2e50a0ffd85c
clean-at-update: true
slice: Carry the published fresh-constructor and reuse schema/witness updates through the direct-let compiler/resource transition, produce a witness-indexed validated successor paired with the updated schema agreement, and use it in the schema-global dispatcher.
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side schema-updating direct-let and schema-global successor theorems only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: active development; not ready for integration
next: Expose the operation-specific schema update alongside the direct-let resource successor, then compose WitnessUpdate.agrees into ConcreteStructuredSchemaValidatedCodeGlobalOutcome.
```
