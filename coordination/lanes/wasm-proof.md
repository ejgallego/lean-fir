# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 132c8bac5a3d355581f432ba9c9d2e50a0ffd85c
functional-head: 34e7b3029735a8dd37983f407d117b0399ceadd5
contract-base: 132c8bac5a3d355581f432ba9c9d2e50a0ffd85c
clean-at-update: true
slice: Carry the published fresh-constructor and reuse schema/witness updates through the direct-let compiler/resource transition, produce a witness-indexed validated successor paired with the updated schema agreement, and use it in the schema-global dispatcher.
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side schema-updating direct-let and schema-global successor theorems only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: git diff --check PASS; Lean Beam sync/save ConcreteCompilerCorrectness, ConcreteReuseCapacityCacheCorrectness, ConcreteStructuredSimulation, ConcreteStructuredValidation PASS; lake build FirTalos.ConcreteStructuredValidation PASS (3127 jobs); make check PASS (730 cases, 2172/2172 comparisons); make talos-setup PASS; make talos-check PASS (3182 jobs, receipt f1fbfffe54952cf6cdd7bad202870953d91713d13c68ccf7bedb199c9faa8437)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: ready for integration; schema-changing direct declarations now retain the exact constructor/reuse update through compiler resources, whole-cache transports, structured execution, residual validation, and ConcreteStructuredSchemaValidatedCodeGlobalOutcome
next: Expose monotone witness extension for the remaining allocating/non-schema direct operations, preserve the current schema there, then assemble the complete schema-global dispatcher.
```
