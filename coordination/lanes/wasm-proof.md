# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: released
base: c170b88cb1c3d8697e57a66ec939e7ea72a1894a
functional-head: 2380ade5bd5701770266086e7e081deeae31d3cc
contract-base: c170b88cb1c3d8697e57a66ec939e7ea72a1894a
clean-at-update: true
slice: Close the constructor-complete validated global one-step simulation, including ordinary code, direct/saturated call entry, lazy hit/miss, external bind, and returned-frame pop. The public ranked simulation now starts from ConcreteSupportedExport.validatedCodeGlobalRoot and preserves ConcreteStructuredValidatedCodeGlobalOutcome, eliminating the unsound universal residual-validation field. Source/phase safety is scoped to validated residual nodes. Finite UInt32 increment headroom and saturated-capture retention were removed from compiler source safety and placed in ConcreteStructuredCurrentStepFiniteRuntimeSafety beside independent allocation address-space safety.
files: bugs/FIR-BUG-wasm-none-finite-trace-refcount-overflow.md; bugs/FIR-BUG-wasm-none-structured-validation-provenance.md; integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteResumableWasm.lean; integration/talos/PLAN.md; coordination/lanes/wasm-proof.md
contracts: No source semantics, concrete layout/runtime, resident-helper signature, symbolic Wasm, or W7 artifact changed. W6 proof interfaces changed: validated provenance is now carried inductively rather than universally reconstructed, and finite header/capture safety is explicitly execution-owned. The address-space law dropped an unused compiler-specification argument.
checks: Lean Beam update/sync/save passed with zero errors for ConcreteStructuredValidation and ConcreteResumableWasm. Forced lake build FirTalos.ConcreteStructuredValidation FirTalos.ConcreteResumableWasm passed all 3,128 jobs. git diff --check passed. make check passed with 730 unique validation cases, 2,172/2,172 comparisons equal, zero findings, 212 active bug cards, and 38 mailbox tests. make talos-setup completed at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check passed all 3,182 jobs with exact receipt 65908df5473988c07a7de67f2e0c953efd83058740bfc575fba7c693c1bf7541.
bug-cards: FIR-BUG-wasm-none-structured-validation-provenance fixed; FIR-BUG-wasm-none-finite-trace-refcount-overflow fixed
blockers: none
handoff: ACCEPTED. Main was fast-forwarded through functional checkpoint 2380ade5bd5701770266086e7e081deeae31d3cc and clean tracked handoff 29106cfd. The provenance-correct ranked simulation and honest finite-runtime boundary are integrated.
next: Resume from accepted main and derive the sole remaining compiler/phase field from a preserved final-LCNF semantic invariant: return value shape, descriptor/local typing, normalized cases, and operation domains. Then package finite runtime and address-space safety from a bounded-resource execution invariant or explicitly budgeted finite prefix.
```
