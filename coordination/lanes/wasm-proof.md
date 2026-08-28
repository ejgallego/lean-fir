# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2693f59350c8f54b3b84b0a7ce1d9bcabe509f02
functional-head: bd03de5b75b680562949eb19c59a483cd60ce34b
contract-base: 2693f59350c8f54b3b84b0a7ce1d9bcabe509f02
clean-at-update: true
slice: Added a schema-aware current-node admission and validated ordinary-code dispatcher. Its guarded legacy arm excludes FVar and erased object-field syntax, so those shapes must use source ConstructorSchema typing plus WitnessAgrees for the active witness.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side admission/readiness boundary only; source semantics, semantic ABI, concrete layout/runtime operations, emitted code, and existing public finite-trace theorem unchanged
checks: git diff --check PASS; Lean Beam sync/save ConcreteStructuredValidation and ConcreteResumableWasm PASS; direct lake env lean on both edited modules PASS; lake build FirTalos.ConcreteStructuredValidation FirTalos.ConcreteResumableWasm PASS (3128 jobs); make check PASS (730 cases, 2172/2172 comparisons); make talos-setup PASS; make talos-check PASS (3182 jobs, receipt b693d7a85cbccd7b4e27252826fbbc8c3e9e4bcc16496788d3ed49115b6d4f5b)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: Land functional commit bd03de5b75b680562949eb19c59a483cd60ce34b and this clean status commit. The ordinary-code dispatcher is schema-aware; the module-global relation is not yet schema-enriched.
next: Add one proof-side witness projection/agreement companion for every constructor of ConcreteStructuredValidatedCodeGlobalOutcome, then preserve it first across witness-unchanged administrative and mutation transitions before allocation/reuse updates.
```
