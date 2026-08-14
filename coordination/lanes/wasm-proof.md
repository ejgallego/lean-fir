# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: c4b21191 on main
functional-head: 4e24c681
contract-base: c4b21191; consumes the landed aligned delete-admission checkpoint and strengthens only W6 proof-side admission/provenance; no runtime, ABI, instruction, or generation semantics changed
clean-at-update: true
slice: Persistent increment and decrement are now complete validator-derived current-step admission cases; production erases both nodes, so no heap, target, or allocation premise is retained. The admission audit rejected an unsound return-contract weakening: leanCompatible alone cannot reclassify a tagged semantic value from tobject to object when the caller local is rebound. It also found that production setTag validation accepts arbitrary Nat while the concrete wasm32 header truncates through UInt32. Both missing compiler-domain facts are documented precisely.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-structured-validation-provenance.md; bugs/FIR-BUG-wasm-none-return-admission-refinement-direction.md; bugs/FIR-BUG-wasm-none-settag-uint32-admission.md; coordination/lanes/wasm-proof.md
contracts: W6 proof-side theorems only. ConcreteStructuredAlignedValidationState gains packaged persistent ownership admission. No source semantics, concrete runtime, Wasm ABI, symbolic instruction, resident helper signature, production validator, or W7-consumed generation surface changed.
checks: Lean Beam update/sync/save PASS with zero errors and zero warnings in ConcreteStructuredValidation; direct lake build FirTalos.ConcreteStructuredValidation PASS (3124 jobs); git diff --check PASS; bug-card validation PASS (181 active cards); make check PASS (125 harness tests, 710 unique cases, 2112/2112 comparisons, zero findings, 25 mailbox tests); make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-structured-validation-provenance (updated); FIR-BUG-wasm-none-return-admission-refinement-direction (triage corrected: needs typing/value-shape invariant, not leanCompatible transport); FIR-BUG-wasm-none-settag-uint32-admission (new, confirmed)
blockers: none for this handoff. Direct let still needs retained impure binder hygiene and collector agreement. Sound setTag admission needs a shared production UInt32 guard. Reverse object-family returns need an upstream typing/value-shape invariant before caller rebinding. Object/scalar field mutation still needs source typing/layout facts.
handoff: Ready for integration. The W6 branch is based on main c4b21191, functional head 4e24c681 is green, and the worktree was clean before this mailbox update.
next: Queue the small setTag validator guard through integration, then make declaration hygiene/type-shape facts proof-visible at the supported-function root so direct-let and return admission can be derived without recursive certificates.
```
