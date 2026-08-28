# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: d9fd630fde2eae513c0909d46002874fd15aeb0f
functional-head: d9fd630fde2eae513c0909d46002874fd15aeb0f
contract-base: d9fd630fde2eae513c0909d46002874fd15aeb0f
clean-at-update: true
slice: Lift resolved external execution into the schema-global relation by proving the returned nextWitness extends the incoming witness and transporting ConstructorSchema.WitnessAgrees across that extension.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side witness-extension successor only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: active
next: Expose the external core's witness-extension proof, return the next witness explicitly from the validated successor, and package it with transported schema agreement.
```
