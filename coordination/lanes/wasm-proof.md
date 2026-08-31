# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2899747e
functional-head: 134dc403
contract-base: 2899747e
clean-at-update: true
slice: Derived the complete zero-allocation ordinary direct-call admission from the recursively validated production outcome and one successful current source step. `DirectInternalCallCompilerAdmission` now retains residual compiler-local agreement, so no local compiler equation is supplied by a client. `ConcreteStructuredDirectCallArgumentsAt` isolates only the current semantic argument row at the compiler-selected callee ABI, and `ConcreteStructuredValidatedCodeOutcome.admit_directCall_of_compiler` reconstructs declaration/result facts, compilation, argument evaluation, parameter binding, and the exact `ConcreteStructuredCodeStepAdmission.directCall` branch.
files: integration/talos/FirTalos/ConcreteFinalLcnfTyping.lean; docs/w6-source-admission-audit.md; docs/pass-correctness-plan.md; coordination/lanes/wasm-proof.md
contracts: W6 proof interface only. The new current-node predicate and PA2 branch theorem add no source semantics, validation/lowering policy, runtime ABI/layout, symbolic instruction, generated-code, ownership, or resident-helper contract change. No future step, target path, global source invariant, or program certificate is introduced.
checks: Lean Beam update/sync/save for FirTalos.ConcreteFinalLcnfTyping (pass: zero blocking diagnostics, six pre-existing linter warnings); lake build FirTalos.ConcreteFinalLcnfTyping (pass: 3129 jobs); git diff --check (pass); make check (pass: 730 unique cases, 2172/2172 comparisons equal, exactly one trusted axiom, mailbox gates green); make talos-setup (pass: Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254); make talos-check (pass: 3190 jobs, exact build receipt d2f741c0d9f7d512ed3e774db64dc9ad2f92dd7a477120f7c8862cde337c5d9c)
bug-cards: none
blockers: The 158 product-observed non-refining argument uses are exactly `tobject -> object`; W7 origin census request `W6-W7-20260831-002` is open to determine the smallest compiler-owned provenance analysis. PA3 also retains return producer origin, closure ingress, lazy-miss backend coverage, and schema/layout-sensitive field gaps.
handoff: clean W6 functional head `134dc403`, based exactly on accepted main `2899747e`; ready for fast-forward integration
next: Use the producer-origin census to construct `ConcreteStructuredDirectCallArgumentsAt` from minimal compiler-owned precise-value analysis for `tobject -> object`, then wire this completed direct-call branch into the whole current-step admission dispatcher.
```
