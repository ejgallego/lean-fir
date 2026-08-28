# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: b54ed3c16f9a2d21c1662e792e60b33ae8d7b16e
functional-head: b54ed3c16f9a2d21c1662e792e60b33ae8d7b16e
contract-base: b54ed3c16f9a2d21c1662e792e60b33ae8d7b16e
clean-at-update: true
slice: Classify direct-let constructor successors by their actual schema delta, lift fresh constructor allocation with ConstructorSchema.WitnessAgrees.bindConstructor, and lift successful reuse with WitnessAgrees.rebindConstructor.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side constructor-schema transition and indexed successor theorems only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: active development; not ready for integration
next: Recover the exact bind/rebind evidence from the direct-let runtime refinement, state the common schema-transition abstraction, and compose it into the schema-global dispatcher.
```
