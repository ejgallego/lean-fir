# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 2d96f096 on main
functional-head: 33b0d83b
contract-base: 2d96f096; consumes the accepted production-selection dispatch, W7 no-placeholder repair, and proof-indexed Array stack; strengthens only the W6 proof-side compiler handle with the exact production local row and changes no runtime, ABI, instruction, or generation semantics
clean-at-update: true
slice: W6 begins validator-derived current-step admission without certificates. Residual validation plus production-local agreement now derives ordinary decrement admission directly from the successful source step; increment has the same derivation with its independent finite-UInt32 headroom premise exposed. A hereditary aligned-validation state and insertion law package the static bridge. The proof-side compiler handle now retains the exact declaration-local row produced by lowerDecl, and both generated internal-function selectors transport that row.
files: integration/talos/FirTalos/ConcreteSupportedExportCorrectness.lean; integration/talos/FirTalos/ConcreteReuseCapacityCacheCorrectness.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; bugs/FIR-BUG-wasm-none-finite-trace-refcount-overflow.md; bugs/FIR-BUG-wasm-none-structured-validation-provenance.md; coordination/lanes/wasm-proof.md
contracts: W6 proof-side handle only: ConcreteSupportedFunction and ConcreteGeneratedInternalDeclaration retain context.localKinds = functionBindings sourceFunction, proved from the executable LoweredInternalDeclaration row. No source semantics, concrete runtime, Wasm ABI, symbolic instruction, resident helper, or W7-consumed generation surface changed.
checks: Lean Beam update/sync/save PASS with zero errors for all edited Lean modules; direct lake build FirTalos PASS (3148 jobs); after rebase onto 2d96f096, git diff main...HEAD --check PASS, make check PASS (125 harness tests, 710 unique cases, 2112/2112 comparisons, zero findings, 25 mailbox tests), and make talos-check PASS (3148 jobs).
bug-cards: FIR-BUG-wasm-none-finite-trace-refcount-overflow (new, confirmed); FIR-BUG-wasm-none-structured-validation-provenance (updated)
blockers: none for this handoff. Universal admission still needs production-root/residual row agreement threaded through the validated relation; return compatibility direction and finite refcount headroom remain explicit follow-ups.
handoff: Ready for integration. The W6 branch is rebased on main 2d96f096, the functional stack through 33b0d83b is green, and the worktree is clean before this mailbox update.
next: Derive production root local agreement from the retained lowering row, preserve it across residual validator transitions, then assemble the syntax-directed current-step admission theorem. Keep finite address-space and reference-count headroom in the separate dynamic safety premise.
```
