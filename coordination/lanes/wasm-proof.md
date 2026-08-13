# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: a348f8ac on main; includes the accepted boxed generic Bool validation contract and all prior W6 pointwise/export-root slices
functional-head: 0946ec49
contract-base: a348f8ac; consumes the accepted structured-Wasm/compiler, source-semantics, concrete-runtime, generated-call, resident-runtime, and validation contracts without changing a shared semantic or executable ABI contract
clean-at-update: true
slice: W6.7f active-result-index slice. `ConcreteSupportedFunction` and production generated rows now retain the exact first symbolic result lane. Supported and runnable global outcomes require that exact lane to equal their active `functionResult`; root construction selects it without a caller argument. Direct named calls distinguish the public declared result ABI from the effective compiler-selected lane. Direct, saturated, and lazy entry derive the callee equality from executable lowering; supported caller frames retain their equality and return/pop restores it. The malformed global states blocking universal admission are no longer constructible, and `FIR-BUG-wasm-none-structured-active-result-index` is fixed.
files: integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean, integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean, integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/FirTalos/ConcreteResumableWasm.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, bugs/FIR-BUG-wasm-none-structured-active-result-index.md, coordination/lanes/wasm-proof.md
contracts: none; strengthens only W6 proof packages and simulation indices. No shared source semantics, symbolic Wasm surface, concrete runtime, resident-helper signature, or executable ABI changed
checks: coherent slice committed as a008a26c and rebased cleanly onto main a348f8ac as functional head 0946ec49; Lean Beam update/sync/save PASS with zero errors and save-ready hashes ConcreteSupportedExportCorrectness df64f9a0f17e3b60, ConcreteReuseCapacityCacheCorrectness 801d7dcdfddfb0e8, ConcreteStructuredSimulation 7e437377310fc4e8, and ConcreteResumableWasm 02a280fd82a550ed; targeted lake build FirTalos.ConcreteResumableWasm PASS; git diff --check PASS before and after rebase; make check PASS before rebase (667 source cases, 676 unique cases, 2010/2010 comparisons, 7271 machine steps, zero findings) and after rebase (125 harness tests, 669/669 native-LCNF, 9/9 direct-machine, 669-case native/LCNF/V8 triangle, 678 unique cases, 2016/2016 comparisons, 7303 machine steps, zero findings, 167 active bug cards, Lean 4.33 trusted-assumption gate); make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check PASS before and after rebase (3143 jobs)
bug-cards: FIR-BUG-wasm-none-structured-active-result-index fixed; FIR-BUG-wasm-none-finite-trace-address-space-safety remains active
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main a348f8ac through functional head 0946ec49 and this mailbox commit; no shared contract changed
next: split compiler-derived current-node admission from the independent `requiredBytes <= remainingBytes` wasm32 safety premise, prove the compiler-admission half over the exact active result index, and close the selected resource-safe or explicitly budgeted finite-prefix theorem. Heap-valued lazy miss publication and target-only loop unwinding remain separate widenings.
```
