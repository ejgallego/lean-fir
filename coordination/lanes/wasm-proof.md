# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 64903ee7 on main; includes the accepted boxed validation-scalar contract and all prior W6 pointwise slices
functional-head: d9d74fdf
contract-base: 64903ee7; consumes the accepted structured-Wasm/compiler, source-semantics, concrete-runtime, generated-call, resident-runtime, and validation contracts without changing a shared semantic or executable ABI contract
clean-at-update: true
slice: W6.7f export-root and theorem-boundary slice. `ConcreteSupportedExport.supportedGlobalRootAt` now constructs the admission-free strong relation at the actual compiler-produced source and structured-Wasm entries from the ordinary concrete cache/ABI frame; both caller stacks are canonical nil and no source evaluation, target path, termination evidence, or future admission is supplied. `ConcreteSupportedExport.finiteTraceCorrect_of_currentStepCoverage` composes that root with the ranked current-step classifier. Proof audit also separates what the remaining coverage premise actually means: current-node admission is compiler-derived, while `requiredBytes <= remainingBytes` is finite wasm32 resource safety and cannot follow from lowering alone. The root's temporary caller-selected result ABI is exposed in its name pending relation indexing.
files: integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/FirTalos/ConcreteResumableWasm.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, bugs/FIR-BUG-wasm-none-finite-trace-address-space-safety.md, bugs/FIR-BUG-wasm-none-structured-active-result-index.md, coordination/lanes/wasm-proof.md
contracts: none; W6 proof-side export-root constructor, conditional finite-trace packaging theorem, precise documentation of the existing combined coverage premise, and two proof-contract bug cards only
checks: committed the coherent slice on b28b05af, then rebased cleanly onto main 64903ee7; Lean Beam update/sync/save PASS before rebase with zero errors and save-ready ConcreteStructuredSimulation hash 233c4ea0d8a6361a and ConcreteResumableWasm hash 111a1c8fc10ffd39; git diff --check PASS before and after rebase; make check PASS before rebase (675 unique cases, 2007/2007 comparisons, 7252 machine steps) and after rebase (125 harness tests, 667/667 native-LCNF, 9/9 direct-machine, 667-case native/LCNF/V8 triangle, 676 unique cases, 2010/2010 comparisons, 7271 machine steps, zero findings, 167 active bug cards, Lean 4.33 trusted-assumption gate); make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check PASS before and after rebase (3143 jobs, including both modified proof modules)
bug-cards: FIR-BUG-wasm-none-finite-trace-address-space-safety; FIR-BUG-wasm-none-structured-active-result-index
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main 64903ee7 through functional head d9d74fdf and this mailbox commit; no shared contract changed
next: strengthen the strong supported-global relation so its active `functionResult` is definitionally tied to the selected symbolic function's singleton result row, preserving/restoring that index through internal call entry and return; then split compiler admission from finite-address-space safety and close the selected resource-safe or explicitly budgeted finite-prefix theorem. Heap-valued lazy miss publication and target-only loop unwinding remain separate widenings.
```
