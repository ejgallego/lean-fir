# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 7fd2d2d9 on main; includes the accepted finite-trace resource boundary and all prior W6 pointwise/export-root/result-index slices
functional-head: f459d5b1
contract-base: 7fd2d2d9; consumes the accepted structured-Wasm/compiler, source-semantics, concrete-runtime, generated-call, resident-runtime, and validation contracts without changing a shared semantic or executable ABI contract
clean-at-update: true
slice: W6.7f structured-validation-provenance slice. Every supported generated function now retains the exact source declaration/body selected by production lowering, its exact effective result ABI, and a theorem reconstructing the real `WasmSupported` body judgment at the active result kind. Generated internal rows retain the same provenance across direct, saturated, and lazy calls. The compiler current-step admission law now receives the active-result equality already stored by the global relation; it no longer drops that compiler invariant at the proof boundary.
files: integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean, integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean, integration/talos/FirTalos/ConcreteStructuredSimulation.lean, integration/talos/FirTalos/ConcreteResumableWasm.lean, integration/talos/PLAN.md, integration/talos/W6-THEOREM-ROADMAP.md, bugs/FIR-BUG-wasm-none-structured-validation-provenance.md, coordination/lanes/wasm-proof.md
contracts: none; strengthens W6 proof-side compiler provenance only. No shared source semantics, symbolic Wasm surface, concrete runtime, resident-helper signature, generated code, or executable ABI changed
checks: functional head f459d5b1 on current main 7fd2d2d9; Lean Beam update/sync/save PASS with zero proof errors for ConcreteSupportedExportCorrectness, ConcreteReuseCapacityCacheCorrectness, ConcreteStructuredSimulation, and ConcreteResumableWasm; targeted lake build FirTalos.ConcreteResumableWasm PASS (3120 jobs); git diff --check PASS; make check PASS (125 harness tests and all coverage/oracle/trusted-assumption gates); make talos-setup PASS at Talos 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check PASS (3143 jobs)
bug-cards: FIR-BUG-wasm-none-structured-validation-provenance confirmed; first invariant repair landed, residual local/join/case/sharing validation state remains
blockers: none
handoff: integration may fast-forward wasm/talos-runtime from main 7fd2d2d9 through functional head f459d5b1 and this mailbox commit; no shared contract changed
next: define the hereditary residual `supportedCodeWithJoins` invariant carrying current local kinds, join points, case facts, and sharing facts alongside `ConcreteStructuredCodeCoreRel`; prove its root from `validatedBodyAt` and advance it across the already-proved structured transitions. Then derive `ConcreteStructuredCompilerCurrentStepAdmission` constructors from that invariant plus the successful source step, independently of wasm32 memory safety.
```
