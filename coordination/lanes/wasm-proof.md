# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 8a0e467f40badd48da0f267eb8efb4f7d3fef814, current main after acceptance of the scalar-boxing source frontier
functional-head: 5b4002c291399a1f8fa84dd7f9127f8a770f98ea
contract-base: 8a0e467f40badd48da0f267eb8efb4f7d3fef814
clean-at-update: true
slice: Repaired the internal named-call proof contract so DirectInternalCallSite.resultCompiled records the authoritative effective callee result kind selected by refineNamedCallLocalKinds. Direct-call declaration induction, cache laws, structured ready/entry focuses, bind frames, resource stacks, supported stacks, validation stacks, and closed staged outcomes now retain that precise kind through callee entry and caller resumption. Public source-result compatibility remains separate at source-facing boundaries. Removed the temporary exact-result equality premise and added a strict object-to-tobject positive regression proving that validator and compiler local rows both select object while the public annotation remains tobject.
files: integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-direct-call-validation-result-kind-drift.md; coordination/lanes/wasm-proof.md
contracts: No shared semantic definition, runtime behavior, ABI, concrete layout, resident helper, emitter, symbolic Wasm instruction, or W7-owned artifact changed. The W6 proof-side DirectInternalCallSite contract is corrected: exact compiler-local layout uses calleeResultKind, while calleeResultRefines independently relates it to the public resultKind. ConcreteStructuredValidatedCodeOutcome.advance_directCall_stage_of_step no longer needs the temporary result-kind equality premise.
checks: Lean Beam sync/save reported zero errors for FirTalos/ConcreteReuseCapacityCacheCorrectness (19 pre-existing warnings), FirTalos/ConcreteStructuredSimulation (18 pre-existing warnings), and FirTalos/ConcreteStructuredValidation (two pre-existing warnings); targeted lake build FirTalos.ConcreteStructuredValidation passed 3,127 jobs after rebase; git diff --check passed; make check passed after rebase with 719/719 source cases across native, LCNF, and V8, 9/9 direct-machine cases, 2,166/2,166 indexed comparisons equal, zero findings, 208 active bug cards, and 26 mailbox tests; make talos-setup fixed Talos at 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check passed all 3,174 jobs.
bug-cards: FIR-BUG-wasm-none-direct-call-validation-result-kind-drift (fixed)
blockers: none
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and integrate the stack based at 8a0e467f through functional head 5b4002c2. The branch is rebased on current main, all gates pass, and only W6-owned proof/bug-card files plus this single-writer mailbox changed.
next: Resume universal finite-trace dispatcher and compiler-admission assembly, using the exact validated local-row relation now established for non-named lets, saturated closure calls, exact named calls, and strictly refined internal named calls.
```
