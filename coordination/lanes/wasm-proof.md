# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2e5779aa7149e3f08151e4c298a5894fb93fadd5
functional-head: bd908f8eda7ffc61a334d727376f56e9915ea863
contract-base: 2e5779aa7149e3f08151e4c298a5894fb93fadd5
clean-at-update: true
slice: Direct and saturated entry, lazy hit/miss, destination bind, and ordinary/lazy return-pop now close in ConcreteStructuredValidatedCodeGlobalOutcomeAt at the exact incoming witness. The legacy global dispatcher erases these stronger results. Resolved external execution is correctly classified as witness-changing because it produces nextWitness.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: additive proof-side successor theorems only; source semantics, semantic ABI, concrete runtime/layout operations, emitted code, and established validated/finite-trace relations unchanged
checks: git diff --check PASS; Lean Beam sync/save ConcreteStructuredValidation and downstream ConcreteResumableWasm PASS; lake build FirTalos.ConcreteStructuredValidation FirTalos.ConcreteResumableWasm PASS (3128 jobs); make check PASS (730 cases, 2172/2172 comparisons); make talos-setup PASS; make talos-check PASS (3182 jobs, receipt cc63d78b6eb09e2e873e7fcd0116e00760e64bd6c1c3a7d4747a891a99680b08)
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission
blockers: none
handoff: Land functional commit bd908f8eda7ffc61a334d727376f56e9915ea863 and this clean status commit. The branch is frozen until integration.
next: Lift resolved external execution through WitnessAgrees.witnessExtension, then cover constructor allocation and reuse via bindConstructor/rebindConstructor before assembling the full schema-global dispatcher.
```
