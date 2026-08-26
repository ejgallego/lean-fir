# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 238d6016ec28aeaa6608a9c544dc36753d7daf48, current main after acceptance of the ElimDead source-only lifecycle proof
functional-head: 45e515c06fe1fc84e2a97dad9cf1fc5e7632f047
contract-base: 238d6016ec28aeaa6608a9c544dc36753d7daf48
clean-at-update: true
slice: Strengthened the closed structured-code relation so active validation, staged direct/saturated/external continuations, and hereditary suspended-call agreement retain exact validator/compiler local-row alignment. Root entry now uses the aligned validator package; ordinary successors and case selection preserve it. One factored non-named-let theorem discharges destination-local agreement for the complete budgeted direct-value family and saturated closure calls. Direct named calls preserve alignment when the validator's effective callee result equals the public destination kind; the strict-refinement contract gap is explicit in the theorem and recorded rather than hidden by a certificate or weakened mutation relation.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-direct-call-validation-result-kind-drift.md; coordination/lanes/wasm-proof.md
contracts: No shared semantic definition, ABI, layout, runtime helper, emitter, symbolic Wasm instruction, or W7-owned artifact changed. The W6 validated relation and proof-facing closed transition theorems are strengthened. ConcreteStructuredValidatedCodeOutcome.advance_directCall_stage_of_step gains the explicit exact-result equality required by the current DirectInternalCallSite contract.
checks: Lean Beam sync/save for FirTalos/ConcreteStructuredValidation reported zero errors (two pre-existing linter warnings); targeted lake build FirTalos.ConcreteStructuredValidation passed 3,127 jobs; git diff --check passed; make check passed after rebase with 719/719 source cases, 9/9 direct-machine cases, 2,166/2,166 indexed comparisons equal, zero findings, 208 active bug cards, and 26 mailbox tests; make talos-setup fixed Talos at 0e05edbcfbb105b33e90c60b4f50e2cf193d9254; make talos-check passed all 3,174 jobs.
bug-cards: FIR-BUG-wasm-none-direct-call-validation-result-kind-drift (confirmed)
blockers: Strictly refined internal named-call results cannot yet extend exact validator/compiler local agreement because DirectInternalCallSite.resultCompiled records the public resultKind while supportedLetDeclKind? selects calleeResultKind. Exact-result named calls and all non-named lets are closed.
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and integrate the stack based at 238d6016 through functional head 45e515c0. The branch is rebased on current main, all gates pass, and only W6-owned proof/bug-card files plus this single-writer mailbox changed.
next: Repair DirectInternalCallSite so its destination equation carries the authoritative compiler local kind selected by refineNamedCallLocalKinds, adapt direct-call staging/resource proofs, add a strict object-family refinement regression, and remove the temporary result-equality premise. Then resume universal finite-trace dispatcher assembly.
```
