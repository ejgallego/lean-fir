# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c477dec00656eda92605d9065c3ccbffa3eeea48
functional-head: ddfecad5afc5c0bcfe8a5d7869bcd1890ed75c01
contract-base: c477dec00656eda92605d9065c3ccbffa3eeea48
clean-at-update: true
slice: Expose monotone witness extension for the remaining non-schema-changing direct operations, preserve the current constructor schema through their structured validated successors, and assemble the complete schema-global direct dispatcher.
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side witness-extension and schema-global direct-dispatch theorems only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: Lean Beam update/sync/save PASS for ConcreteCompilerCorrectness, ConcreteReuseCapacityCacheCorrectness, ConcreteStructuredSimulation, and ConcreteStructuredValidation; lake build FirTalos.ConcreteStructuredValidation PASS (3127 jobs); git diff --check PASS; make check PASS (730 cases, 2172/2172 comparisons); make talos-setup PASS; make talos-check PASS (3182 jobs, receipt 892f942460716ba3d7d6790ca6b3fb73d44e7935f304c79bd744004f48965b04)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: ready for integration; every schema-preserving production direct primitive now exposes monotone witness extension through compiler/resource, cache, structured, and validated layers; the exact production admission split combines it with schema-changing constructor/reuse in one schema-global direct successor; no shared semantic/runtime/emission contract changed
next: Strengthen the outer code dispatcher to return ConcreteStructuredSchemaValidatedCodeGlobalOutcome in every branch, using the new complete direct successor with the established administrative, external, and schema-derived object-field successors; then retire the legacy module-global effect-admission surface.
```
