# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: ab0845d3 on main
functional-head: 946e81aa
contract-base: ab0845d3; consumes the landed hereditary aligned-validation checkpoint and strengthens only W6 proof-side admission/provenance; no runtime, ABI, instruction, or generation semantics changed
clean-at-update: true
slice: Explicit deletion admission is now derived from the aligned validator state plus the actual successful source step: validation supplies the exact ordinary-object compiler lane, while the source step supplies the semantic lookup and delete update. Compiler/validator local agreement is also preserved through delete, constructor-tag, object-field, USize-field, and packed-scalar-field continuations. Attempting the direct-let collector bridge exposed and documented the missing body-binder hygiene boundary instead of weakening local-kind equality.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-structured-validation-provenance.md; bugs/FIR-BUG-wasm-none-local-binder-name-uniqueness.md; coordination/lanes/wasm-proof.md
contracts: W6 proof-side theorems only. ConcreteStructuredAlignedValidationState gains non-binding mutation continuation transport and packaged explicit-delete admission. No source semantics, concrete runtime, Wasm ABI, symbolic instruction, resident helper signature, or W7-consumed generation surface changed.
checks: Lean Beam update/sync/save PASS with zero errors and zero warnings in ConcreteStructuredValidation; direct lake build FirTalos.ConcreteStructuredValidation PASS (3124 jobs); git diff --check PASS; bug-card validation PASS (180 active cards); make check PASS (125 harness tests, 710 unique cases, 2112/2112 comparisons, zero findings, 25 mailbox tests); make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-structured-validation-provenance (updated); FIR-BUG-wasm-none-local-binder-name-uniqueness (new, confirmed)
blockers: none for this handoff. Direct-let result-slot agreement is blocked for arbitrary raw supported input because supportedDecl does not retain body-binder hygiene and collectLocalsCore replaces duplicate names. The repair should retain/check the existing impure hygiene invariant and prove collector agreement from it; join, case, call-entry, and suspended-frame alignment remain independent follow-ups.
handoff: Ready for integration. The W6 branch is based on main ab0845d3, functional head 946e81aa is green, and the worktree was clean before this mailbox update.
next: Coordinate the binder-hygiene proof boundary needed by direct let, while continuing sound validator-derived admission and alignment transport for non-binding mutation and suspended control-flow nodes.
```
