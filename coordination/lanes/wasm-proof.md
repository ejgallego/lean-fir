# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8bcafc05 on main; includes the accepted generic-container validation slice and all prior W6 pointwise/export-root/result-index slices
functional-head: 379d8202
contract-base: 8bcafc05; consumes the accepted structured-Wasm/compiler, source-semantics, concrete-runtime, generated-call, resident-runtime, and validation contracts without changing a shared semantic or executable ABI contract
clean-at-update: true
slice: W6.7f admission/resource-boundary slice. `ConcreteStructuredCompilerCurrentStepAdmission` now recovers only source/compiler admission and its exact cost. `ConcreteStructuredCurrentStepAddressSpaceSafety` independently states that an admitted cost fits the current wasm32 budget. Their classifier and finite-trace composition is proved, the legacy coverage package is only a compatibility pair, and `ConcreteSupportedExport.finiteTraceCorrect_of_currentStepAdmission` is the preferred export theorem with the two hypotheses visibly separate. The compiler field can no longer inherit an unprovable finite-memory obligation.
files: integration/talos/FirTalos/ConcreteResumableWasm.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, bugs/FIR-BUG-wasm-none-finite-trace-address-space-safety.md, coordination/lanes/wasm-proof.md
contracts: none; restructures W6 proof-side theorem packages only. No shared source semantics, symbolic Wasm surface, concrete runtime, resident-helper signature, or executable ABI changed
checks: functional head 379d8202 on current main 8bcafc05; Lean Beam update/sync/save PASS with zero proof errors (a later dependency-cache resync hit read-only restored `.ilean` files, while direct batch replay remained green); targeted lake build FirTalos.ConcreteResumableWasm PASS (3120 jobs); git diff --check PASS; make check PASS (125 harness tests, 676/676 native-LCNF, 9/9 direct-machine, 676-case native/LCNF/V8 triangle, 685 unique cases, 2037/2037 comparisons, 7341 machine steps, zero findings, 167 active bug cards, Lean 4.33 trusted-assumption gate); make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check PASS (3143 jobs)
bug-cards: FIR-BUG-wasm-none-finite-trace-address-space-safety fixed; none active from this slice
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main 8bcafc05 through functional head 379d8202 and this mailbox commit; no shared contract changed
next: prove `ConcreteStructuredCompilerCurrentStepAdmission` for the currently admitted production fragment, closing compiler-derived code-node inversion independently of memory. Join/jump control, heap-valued lazy miss publication, and target-only loop unwinding remain explicit proof widenings. Then discharge `ConcreteStructuredCurrentStepAddressSpaceSafety` from either a resource-safe execution invariant or an explicitly budgeted finite source prefix.
```
