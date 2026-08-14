# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: bebc9b53 on main
functional-head: 69e054f9
contract-base: bebc9b53; no shared-contract change
clean-at-update: true
slice: Object-field mutation now has a precise source-typing boundary and complete current-step admission for both FVar and erased payloads under that boundary. Residual validation supplies the compiler-selected lanes; one successful source step supplies the live constructor and slot bound; `ConcreteObjectFieldKindAligned` supplies only the missing descriptor-slot kind. The proof inspects no target path and stores no translation certificate. Proof inversion also confirms that production raw-LCNF validation does not currently establish this fact.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-object-field-kind-admission.md; coordination/lanes/wasm-proof.md
contracts: none. No source semantics, production validator, concrete runtime/layout, Wasm ABI, symbolic instruction, resident helper signature, emitted code, or W7 generation surface changed.
checks: Lean Beam update/sync/save PASS with zero errors and zero warnings in ConcreteStructuredValidation; direct lake build FirTalos.ConcreteStructuredValidation PASS (3124 jobs); bug-card validation PASS (182 active cards); git diff --check PASS; make check PASS (125 harness tests, 710 unique cases, 2112/2112 comparisons, zero findings, 25 mailbox tests); make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-object-field-kind-admission (confirmed)
blockers: Production admission does not yet derive the descriptor-kind invariant; accepted raw LCNF can mismatch an `.oset` payload and descriptor slot. Packed scalar mutation similarly still needs `ScalarFieldMutationSafe` layout evidence. Direct let still needs retained impure binder hygiene and collector agreement. Reverse object-family returns need an upstream typing/value-shape invariant before caller rebinding.
handoff: Ready for integration. The W6 branch is based directly on main bebc9b53, functional head 69e054f9 is green, and the worktree was clean before this mailbox update.
next: Design the smallest source typing/provenance invariant that establishes descriptor kinds through constructor/reuse creation, aliases, joins, and calls. Queue any production-validator change as an isolated shared contract; do not turn the invariant into a per-translation certificate.
```
