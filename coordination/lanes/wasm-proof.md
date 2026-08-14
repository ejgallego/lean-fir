# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7bd19a22 on main
functional-head: 9a336bfc
contract-base: 7bd19a22; consumes the landed production-root aligned-validation bridge and strengthens only W6 proof-side hereditary provenance; no runtime, ABI, instruction, or generation semantics changed
clean-at-update: true
slice: W6 begins hereditary admission over the compiler-derived aligned invariant. Direct let continuation extends validator/compiler local agreement with the exact result binding selected by both sides. Ordinary increment and decrement admission now consume the aligned residual package directly, and both ownership forms preserve that package through their continuations. UInt32 reference-count headroom remains an explicit independent dynamic premise for increment.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-structured-validation-provenance.md; coordination/lanes/wasm-proof.md
contracts: W6 proof-side theorems only. ConcreteStructuredAlignedValidationState gains let/inc/dec continuation transport and packaged ordinary ownership admission. No source semantics, concrete runtime, Wasm ABI, symbolic instruction, resident helper signature, or W7-consumed generation surface changed.
checks: Lean Beam sync/save PASS with zero errors and zero warnings in ConcreteStructuredValidation; direct lake build FirTalos.ConcreteStructuredValidation PASS (3124 jobs); git diff --check PASS; make check PASS (125 harness tests, 710 unique cases, 2112/2112 comparisons, zero findings, 25 mailbox tests); make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-structured-validation-provenance (updated)
blockers: none for this handoff. The direct-let compiled-binding premise still needs to be discharged from operation-specific adaptation; join, case, call-entry, and suspended-frame alignment remain. Return compatibility direction and finite refcount headroom are explicit independent follow-ups.
handoff: Ready for integration. The W6 branch is based on main 7bd19a22, functional head 9a336bfc is green, and the worktree was clean before this mailbox update.
next: Derive the direct-let result binding from concrete operation adaptation, then preserve aligned validation across join/case/call-entry and suspended-frame transitions before assembling the syntax-directed current-step admission theorem.
```
