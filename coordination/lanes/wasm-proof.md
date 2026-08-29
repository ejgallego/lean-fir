# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: 9301c0e0284f605ccad0f089240058c44a044352
functional-head: 9301c0e0284f605ccad0f089240058c44a044352
contract-base: 9301c0e0284f605ccad0f089240058c44a044352
clean-at-update: true
slice: Define the source-only constructor-schema step relation, retain that exact transition through schema-global validated advancement, and package the paired hereditary source invariant needed for the ranked finite-trace simulation.
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side source-schema transition and invariant interfaces only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: active development; not ready for integration
next: Factor the source-determined schema successor from DirectLetUpdate, lift identity transitions for every other outcome, and prove the schema-indexed invariant/simulation composition.
```
