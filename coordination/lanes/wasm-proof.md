# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 14286b61
functional-head: 52f01fea
contract-base: 14286b61
clean-at-update: true
slice: Retained the production-derived `ConcreteResidualLocalAlignment` inside every active aligned validation state. Root construction is compiler-derived; lets remove the exact head row; layout-neutral mutation and ownership nodes use one generic reindexing rule; selected case alternatives inherit their traversal subrow; suspended callers retain the strengthened aligned state. Lazy admission now projects its destination lane from the current recursively validated outcome.
files: integration/talos/FirTalos/ConcreteResidualLocalAlignment.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: proof-only `ConcreteStructuredAlignedValidationState` now includes compiler-derived residual-local alignment. Source semantics, production acceptance, public runtime ABI/layout, symbolic instructions, generated code, ownership, and resident-helper signatures are unchanged.
checks: Lean Beam refresh/save for ConcreteResidualLocalAlignment, ConcreteStructuredValidation, and ConcreteFinalLcnfTyping (pass: zero errors; only pre-existing validation warnings); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3129 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3190 jobs, exact build receipt 297f1b59ac2c94f2962f88086eca918d0baa80eaa6b2c28581d8f4360e52cb72)
bug-cards: none
blockers: Lazy misses accepted by production but implemented by an external initializer or returning `.object`/`.tobject` remain a genuine backend-coverage gap. PA3 also retains the known producer-origin, closure-ingress, and schema/layout-sensitive field gaps.
handoff: clean W6 functional head `52f01fea`, based exactly on accepted main `14286b61`; ready for fast-forward integration
next: Assemble the now-closed lazy-hit branch into `ConcreteStructuredCompilerCurrentStepAdmission`, then continue the remaining class-C producer/object proofs without reintroducing a caller source invariant.
```
