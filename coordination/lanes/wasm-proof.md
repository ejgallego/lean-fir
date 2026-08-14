# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 49b56a0d on main
functional-head: e8def3a8
contract-base: 49b56a0d; consumes released contract WASM-SETTAG-UINT32-ADMISSION at isolated validator commit 982ed402 and changes only its W6 proof consumer
clean-at-update: true
slice: Constructor-tag mutation is now a complete validator-derived current-step admission case. The residual validator supplies the exact wasm32 range and ordinary-object local facts; one successful source step exposes the semantic heap reference, live constructor cell, and update. The assembled admission reuses the existing ConstructorTagEffectSupported theorem and inspects no target path. The corresponding truncation bug card is fixed.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-settag-uint32-admission.md; coordination/lanes/wasm-proof.md
contracts: consumes WASM-SETTAG-UINT32-ADMISSION without further contract changes. No source semantics, production validator, concrete runtime/layout, Wasm ABI, symbolic instruction, resident helper signature, emitted code, or W7 generation surface changed.
checks: Lean Beam update/sync/save PASS with zero errors and zero warnings in ConcreteStructuredValidation; direct lake build FirTalos.ConcreteStructuredValidation PASS (3124 jobs); git diff --check PASS; bug-card validation PASS (181 active cards); make check PASS (125 harness tests, 710 unique cases, 2112/2112 comparisons, zero findings, 25 mailbox tests); make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-settag-uint32-admission (fixed)
blockers: none for this handoff. Direct let still needs retained impure binder hygiene and collector agreement. Reverse object-family returns need an upstream typing/value-shape invariant before caller rebinding. Object/scalar field mutation still needs source typing/layout facts.
handoff: Ready for integration. The W6 branch is based directly on main 49b56a0d, functional head e8def3a8 is green, and the worktree was clean before this mailbox update.
next: Derive the field-mutation admission cases from residual validation and successful source steps, isolating only the genuinely missing source typing/layout premise before returning to direct-let and return admission.
```
