# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 9301c0e0284f605ccad0f089240058c44a044352
functional-head: d20971e69dbe0790edd2567436274af1f8a92116
contract-base: 9301c0e0284f605ccad0f089240058c44a044352
clean-at-update: true
slice: Close the schema-indexed finite-trace proof framework: exact compiled-layout constructor/reuse evolution, proved identity evolution for every other source control, transition-retaining ordinary and administrative dispatch, hereditary invariant advancement, and direct construction of the ranked simulation and ConcreteFiniteTraceCorrect.
files: integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side source-schema transition and invariant interfaces only; DirectLetShape now records the compiler's exact compileArgs result; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established compatibility relations unchanged
checks: git diff --check (pass); lake build FirTalos.ConcreteResumableWasm (pass, 3128 jobs); make check (pass, 730 unique validation cases and 2172/2172 equal comparisons); make talos-setup (pass, Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass, 3182 jobs)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: ready for integration from clean branch wasm/talos-runtime at the containing status commit
next: Instantiate the framework from a final-LCNF semantic type/provenance invariant, discharge finite runtime/address-space laws, then retire the legacy module-global compatibility route after production adopts the theorem.
```
