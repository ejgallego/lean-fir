# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 9437d653 on main
functional-head: de17d643
contract-base: 9437d653; consumes the landed validator-derived admission foundation and proof-indexed Array stack; strengthens only W6 proof-side production provenance and changes no runtime, ABI, instruction, or generation semantics
clean-at-update: true
slice: W6 closes the production-root admission bridge without certificates. ConcreteSupportedFunction now identifies its selected symbolic function with its named source declaration; successful production lowering and compiler-derived function-name uniqueness recover the exact LoweredInternalDeclaration. Root validation and lowering compute the same parameter row, duplicate-free name lookup survives the validator/compiler reversal and appended body locals, and ConcreteSupportedFunction.rootAlignedValidationState constructs residual root validation plus production-local agreement with no caller-supplied row premise.
files: integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-structured-validation-provenance.md; coordination/lanes/wasm-proof.md
contracts: W6 proof-side handle only: ConcreteSupportedFunction and ConcreteGeneratedInternalDeclaration retain sourceFunction.name = sourceDeclaration.name/declaration.name. This is a compiler-derived production-selection identity. No source semantics, concrete runtime, Wasm ABI, symbolic instruction, resident helper signature, or W7-consumed generation surface changed.
checks: Lean Beam update/sync/save PASS with zero errors and zero warnings in ConcreteStructuredValidation; direct lake build FirTalos.ConcreteStructuredValidation FirTalos PASS (3148 jobs); git diff --check PASS; make check PASS (125 harness tests, 710 unique cases, 2112/2112 comparisons, zero findings, 25 mailbox tests); make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-structured-validation-provenance (updated)
blockers: none for this handoff. Universal admission still needs aligned validation preserved across residual code/frame transitions; return compatibility direction and finite refcount headroom remain explicit independent follow-ups.
handoff: Ready for integration. The W6 branch is based on main 9437d653, functional head de17d643 is green, and the worktree is clean before this mailbox update.
next: Preserve ConcreteStructuredValidationLocalsAgree across let, join, case, call-entry, and suspended-frame transitions, then assemble the syntax-directed current-step admission theorem. Keep finite address-space and reference-count headroom in the separate dynamic safety premise.
```
