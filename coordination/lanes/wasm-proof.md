# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 8b2b2a9c1c8ce5f3e552147d0f38bb3f54b65ff0
functional-head: 8b2b2a9c1c8ce5f3e552147d0f38bb3f54b65ff0
contract-base: 8b2b2a9c1c8ce5f3e552147d0f38bb3f54b65ff0
clean-at-update: true
slice: Strengthen the outer validated code dispatcher to return ConcreteStructuredSchemaValidatedCodeGlobalOutcome in every established branch, composing the complete direct successor with witness-indexed administrative, external, and schema-derived object-field successors.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive schema-global proof dispatcher only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, compiler admission, and established validated/finite-trace relations unchanged
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: active development; not ready for integration
next: Factor the top-level schema-global dispatcher over current-node admission, then audit which legacy effect-admission premise remains reachable.
```
