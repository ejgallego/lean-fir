# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 07bb4961 on main
functional-head: 9e9e7ad9
contract-base: 07bb4961; the existing shared raw-bit Float32/Float value, ABI, and packed-layout contracts are unchanged
clean-at-update: true
slice: Float32 and Float packed-field projection and mutation now cross the same certificate-free W6 boundary as the four unsigned integer widths. `ValueRel` carries exact raw bits; 4-byte and 8-byte checked reads/writes preserve the live-heap relation, ownership, persistence, capacity, cache, and fault invariants; resolver/compiler/structured-step proofs admit both kinds under the existing scalar-layout judgment. Direct regressions round-trip Float32 negative zero (`0x80000000`) and a noncanonical Float NaN (`0x7ff8000000000042`) without host floating conversion.
files: Fir/Wasm/Concrete/{Refinement,ProjectionCorrectness,ScalarMutationCorrectness,MutationHeapCorrectness,ClosureOwnershipCorrectness,PersistenceCorrectness}.lean; integration/talos/FirTalos/{ConcreteRuntime,ConcreteResolver,ConcreteCompilerCorrectness,ConcreteStructuredSimulation,ConcreteFaultCorrectness,ConcreteReuseCapacityCacheCorrectness,ConcreteRuntimeExamples}.lean; integration/talos/{PLAN.md,README.md,W6-COVERAGE.md}; bugs/FIR-BUG-wasm-none-float-runtime-gap.md; coordination/lanes/wasm-proof.md
contracts: none. This additively completes the W6 concrete-host/refinement coverage for the already-landed raw-bit Float32/Float scalar, ABI, and packed-layout contracts. No source semantics, production validator, physical layout, symbolic Wasm instruction, resident-helper signature, emitted code, or W7 generation surface changed.
checks: Lean Beam update/sync/save checkpoints PASS for the edited concrete proof modules; focused direct builds of FirTalos.ConcreteCompilerCorrectness, FirTalos.ConcreteReuseCapacityCacheCorrectness, FirTalos.ConcreteStructuredSimulation, and FirTalos.ConcreteFaultCorrectness PASS. After rebasing onto main 07bb4961: git diff --check PASS; git diff --check main...HEAD PASS; make check PASS (125 harness tests, 711 unique cases, 2115/2115 comparisons equal, zero findings, 187 active bug cards, 25 mailbox tests); make talos-setup PASS at Talos 0e05edbc; make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-float-runtime-gap (fixed)
blockers: none for packed Float32/Float projection and mutation. Float box/unbox operation coverage and generated W7 float-field artifact fixtures remain separate follow-ups.
handoff: Ready for the active wasm-gen integration owner. Functional head 9e9e7ad9 is rebased directly on main 07bb4961, all required post-rebase gates pass, and the worktree was clean before this mailbox update. The slice is additive for W7: rebase and consume the widened concrete refinement without an ABI, layout, helper, or artifact adaptation.
next: Let W7 add generated raw-bit Float32/Float field fixtures against this boundary; on W6, return to the certificate-free global relation and the open resident Array call/bounds audits. Treat Float box/unbox as a separate operation-family slice.
```
