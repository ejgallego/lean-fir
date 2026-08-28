# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: active
base: c477dec00656eda92605d9065c3ccbffa3eeea48
functional-head: c477dec00656eda92605d9065c3ccbffa3eeea48
contract-base: c477dec00656eda92605d9065c3ccbffa3eeea48
clean-at-update: true
slice: Expose monotone witness extension for the remaining non-schema-changing direct operations, preserve the current constructor schema through their structured validated successors, and assemble the complete schema-global direct dispatcher.
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side witness-extension and schema-global direct-dispatch theorems only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: pending
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: active development; not ready for integration
next: Factor a direct-law extension strengthening for operations other than reuse, then compose WitnessAgrees.witnessExtension in the validated direct branch.
```
