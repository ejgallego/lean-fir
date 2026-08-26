# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 0c37e6d3902cf63c5baf2c81d2b54f8807897e24, current main after validated effect-step acceptance
functional-head: f3e4e5bcac64012f02f96c2e85f8ca1a45e3d08c
contract-base: 0c37e6d3902cf63c5baf2c81d2b54f8807897e24
clean-at-update: true
slice: Extends the pending validated-case stack with the first certificate-free structured join primitive. CodeAdapted.jp_eq inverts the actual recursive compiler and numeric adapter: the continuation is exactly the body of a named zero-arity Wasm block, while the separately compiled join body follows that block. CodeAdaptedWithSuffix.jp_eq retains the physical suffix on the join-body side. ConcreteStructuredCodeFocus.advance_joinIntroduction then proves that one source `.jp` step is matched by exactly one StructuredWasmStep.enterBlock transition, preserves the concrete store/local/refinement relation, exposes the extended source join environment and named adapter label, and records the saved compiled join body in the target label frame. It assumes no target path, translation certificate, future execution, or termination evidence.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; integration/talos/FirTalos/ConcreteCompilerCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; coordination/lanes/wasm-proof.md
contracts: No shared source semantics, executable runtime behavior, compiler ABI, concrete memory layout, resident-helper signature, emitter, symbolic Wasm instruction, or W7 artifact changed. The case dispatcher plus CodeAdapted.jp_eq, CodeAdaptedWithSuffix.jp_eq, and ConcreteStructuredCodeFocus.advance_joinIntroduction are additive W6 proof-side interfaces derived from the existing production compiler and structured target step relation.
checks: The prior case-dispatch commit was fully green after rebasing onto main 0c37e6d3. For the join slice, Lean Beam sync/save accepted ConcreteCompilerCorrectness with zero errors; its prescribed stale-direct-dependency recovery checkpointed that module. The large ConcreteStructuredSimulation diagnostics barrier remained incomplete after the dependency edit, so the required targeted batch build lake build FirTalos.ConcreteStructuredSimulation was run twice and passed all 3,126 jobs after the final cleanup. git diff --check passed; make check passed with 719/719 source cases across native, LCNF, and V8, 9/9 direct-machine cases, 728 unique cases, 2,166/2,166 comparisons equal, zero findings, 209 active bug cards, and 31 mailbox tests; make talos-check passed all 3,174 jobs.
bug-cards: FIR-BUG-impure-case-table-selector-determinism (existing; names the missing final-LCNF normalization phase bridge); FIR-BUG-wasm-none-return-admission-refinement-direction (existing; semantic transport and state-local return-safety boundaries solved; the global source-typing invariant/module dispatcher remains)
blockers: none
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and fast-forward cumulative functional head f3e4e5bc, based directly at 0c37e6d3. This includes the earlier validated-case functional head effb18a6. The worktree is clean at this update and all required gates pass.
next: Define the reusable active-label relation aligning compiler join contexts, named/anonymous adapter labels, and concrete StructuredWasmFrame.label prefixes; use it to prove exact branch unwinding and `.jmp` argument/local transfer; lift join introduction and jump transfer through the hereditary resource/validation stacks; connect the already-proved let/call staging families behind the same uniform successor shape; assemble the module-wide validated one-step dispatcher; preserve source typing/address safety; then lift to ConcreteFiniteTraceCorrect.
```
