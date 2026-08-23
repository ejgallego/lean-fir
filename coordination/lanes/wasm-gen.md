# wasm-gen lane

The forward-looking W7 plan lives in
[`Fir/Wasm/Emit/ROADMAP.md`](../../Fir/Wasm/Emit/ROADMAP.md). Accepted milestone
history remains on `coordination/BOARD.md`; this mailbox records the current
single-writer W7 handoff.

```text
lane: wasm-gen
owner: wasm-gen
branch: wasm/generation
worktree: .worktrees/wasm-generation
state: blocked
base: a2ef2d42 on clean local main, including accepted trusted ByteArray calls and production profile refresh
functional-head: 203806bb, rebased opt-in early finite-target closure lowering
contract-base: a2ef2d42. No Lean semantics, concrete layout, resident-helper signature, semantic Wasm ABI, source entry, adapter API, ownership contract, arena contract, or generic opaque-closure behavior changed. Closed packages now derive module-local closureDispatch and closureDescriptors tables from retained operations; W6 proof adaptation is required before integration
clean-at-update: true
slice: Threaded the final-LCNF pap target set into compileClosureDispatch at the existing closed package capability. Candidate declarations are filtered once per module; ordinary lower and lowerDecl retain the all-target path. The existing structural pass remains as a fail-closed validator. The closed module's exact retained closure operations determine its module-local target and descriptor tables
files: Fir/Wasm/Lower.lean; Fir/Wasm/WellFormed.lean; Fir/Wasm/Emit/Source.lean; Fir/Wasm/Emit/SourceExamples.lean; Fir/Wasm/Emit/ROADMAP.md; coordination/lanes/wasm-gen.md
contracts: Raw lean-zip retains 734 candidates and removes 10888 without constructing them. Its closed metadata is 23 dispatch rows and 38 descriptor rows versus generic 439 and 194. Replacing only those two module-local arrays with the generic post-pass arrays makes the complete symbolic module exactly equal; normalized encoded bytes are exact. Generic opaque-ingress lowering is unchanged
performance: Preserving historical all-target metadata erased the optimization and was rejected. With exact retained metadata, one noisy controlled raw run measured generic lowering at 30929ms and finite-target lowering at 18443ms. Host load varied heavily; this is directional evidence, not a stable percentage claim
checks: No system /tmp input was used; the exact comparison lives under ignored integration/lean-zip/.deps/experiments/closure-dispatch-v2. Lean Beam PASS with zero diagnostics for Lower, WellFormed, Source, and SourceExamples. Focused SourceExamples and lean-zip dependency-cone builds PASS. After rebasing on a2ef2d42, git diff --check PASS and make check PASS with 713 unique cases and 2121/2121 comparisons. make talos-setup PASS at pinned Talos 0e05edbc. make talos-check again reaches the W6-owned ConcreteClosureDispatch theorem and fails only at line 450 because its candidatesEq premise is hard-coded to context.program.decls rather than the new context-selected declarations; all preceding 3157 jobs pass
bug-cards: none; no semantic discrepancy was observed
blockers: W6 must adapt ConcreteClosureDispatch.instructions_compileClosureDispatch to the selected declaration array and state the closed-ingress premise. Until that proof compiles and Talos passes, this shared candidate must not land and dependent prettyM/lean-zip ratchets must not publish
handoff: Shared candidate is rebased at 203806bb on wasm/generation with tracked status at the containing branch head. It is not integration-ready. W6 may rebase or cherry-pick this standalone commit for proof adaptation; integration then validates the atomic shared-plus-proof stack before any consumer metadata/package update
next: W6 proof adaptation; rerun all Talos jobs; then regenerate prettyM and lean-zip contracts and complete artifact gates as separate W7 consumer commits. The accepted production attribution at a2ef2d42 selects a further prettyM constructor-allocation probe after this milestone; the lean-zip shared-decrement candidate remains investigation-only because controlled elapsed evidence regressed and exact profiles did not show reliable decrement movement
```
