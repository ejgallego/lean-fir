# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 300f8ab8 on main
functional-head: b39d185d
contract-base: 300f8ab8; no shared-contract change
clean-at-update: true
slice: Packed scalar mutation now has a precise source/runtime layout-typing boundary and complete current-step admission under that boundary. Residual validation supplies the object lane, payload ABI, matching source annotation, and accepted scalar family; one successful source step supplies the scalar payload, live constructor, and semantic update. `ConcreteScalarFieldLayoutAligned` supplies only the missing packed-region start, extent, and non-overlap facts. The proof inspects no target path and stores no translation certificate. Proof inversion confirms that production raw-LCNF validation does not establish these facts and separately exposes that Float32/Float remain outside the current concrete mutation theorem.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-scalar-field-layout-admission.md; coordination/lanes/wasm-proof.md
contracts: none. No source semantics, production validator, concrete runtime/layout, Wasm ABI, symbolic instruction, resident helper signature, emitted code, or W7 generation surface changed.
checks: Lean Beam update/sync/save PASS with zero errors and zero warnings in ConcreteStructuredValidation; direct lake build FirTalos.ConcreteStructuredValidation PASS (3124 jobs); after the final rebase, git diff --check PASS, make check PASS (125 harness tests, 710 unique cases, 2112/2112 comparisons, zero findings, 183 active bug cards, 25 mailbox tests), and make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-scalar-field-layout-admission (confirmed)
blockers: Production admission does not derive packed scalar coordinates, extent, or overlap safety; accepted raw LCNF can write outside `CtorInfo.ssize` or overlap a retained semantic scalar. Float32/Float scalar writes are accepted by production validation but remain a separate concrete-proof coverage gap. Direct let still needs retained impure binder hygiene and collector agreement. Reverse object-family returns need an upstream typing/value-shape invariant before caller rebinding.
handoff: Ready for the active multi-lane integration owner after the currently serialized candidates. The W6 branch is based directly on main 300f8ab8, functional head b39d185d is green, and the worktree was clean before this mailbox update. No shared contract or proof-owned dependency changed during the rebase.
next: Extend the concrete scalar-mutation refinement to Float32/Float or prove the source layout invariant compositionally through constructor/reuse creation, aliases, joins, and calls. Queue any production-validator or source-typing change as an isolated shared contract; do not turn the invariant into a per-translation certificate.
```
