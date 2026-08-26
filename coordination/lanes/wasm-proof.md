# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: e2c2f8c4dc6f9ac0375b0b4afd50748d6a69e135, current main after representation-aware release acceptance
functional-head: 41ea9105602e920d3aaf6525b47bcdb36cfa0af3
contract-base: e2c2f8c4dc6f9ac0375b0b4afd50748d6a69e135
clean-at-update: true
slice: Retains residual production validation across lazy-cache hit/miss staging and pure external calls; factors return correctness through SemanticValueAtAbi and PhysicalValueRel.ofSemanticValueAtAbi; introduces the source-only, state-indexed ConcreteStructuredReturnValueSafeAt invariant; and derives closed validated successor theorems for return, ordinary increment/decrement/delete, constructor-tag mutation, object-field mutation, USize-field mutation, and scalar-field mutation. The public effect theorems reconstruct compiler-local equations, operation admission, and target paths from residual validation and the source step. Their remaining premises are semantic source typing or genuine runtime safety conditions: wasm32 reference-count headroom for increment, object-field kind alignment/typing, and scalar-field mutation typing. Each theorem preserves the global validated-code outcome and gives the exact concrete target transition.
files: integration/talos/FirTalos/ConcreteRuntime.lean; integration/talos/FirTalos/ConcreteStructuredSimulation.lean; integration/talos/FirTalos/ConcreteStructuredValidation.lean; coordination/lanes/wasm-proof.md
contracts: No shared source semantics, executable runtime behavior, compiler ABI, concrete memory layout, resident-helper signature, emitter, symbolic Wasm instruction, or W7 artifact changed. SemanticValueAtAbi, ConcreteStructuredReturnValueSafeAt, and the validator-derived successor theorems are additive W6 proof-side interfaces. Existing lower-level admission theorems remain available.
checks: Lean Beam update/sync/save and the forced post-rebase refresh reported zero errors for ConcreteStructuredValidation (two pre-existing warnings); targeted lake build FirTalos.ConcreteStructuredValidation passed 3,127 jobs before rebase; the six-commit W6 stack rebased cleanly onto main e2c2f8c4; git diff --check and git diff main...HEAD --check passed; post-rebase make check passed with 719/719 source cases across native, LCNF, and V8, 9/9 direct-machine cases, 728 unique cases, 2,166/2,166 comparisons equal, zero findings, 209 active bug cards, and 31 mailbox tests; post-rebase make talos-check passed all 3,174 jobs.
bug-cards: FIR-BUG-wasm-none-return-admission-refinement-direction (existing; semantic transport and state-local return-safety boundaries solved; the global source-typing invariant/module dispatcher remains)
blockers: none
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and fast-forward the complete pending W6 stack through functional head 41ea9105, based directly at e2c2f8c4. The branch is rebased on current main and all required gates pass.
next: Derive case dispatch from residual validation plus the source step; close let/call and join/jump control-flow cases; assemble the module-wide validated one-step dispatcher; prove preservation of source semantic typing and finite address-space safety; then lift the dispatcher to ConcreteFiniteTraceCorrect.
```
