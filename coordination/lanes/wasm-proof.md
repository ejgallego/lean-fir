# wasm-proof lane

```text
lane: wasm-proof
owner: wasm-proof
branch: wasm/talos-runtime
worktree: .worktrees/wasm-talos
state: ready
base: 0c37e6d3902cf63c5baf2c81d2b54f8807897e24, current main after validated effect-step acceptance
functional-head: effb18a69aee7a39b466c309707726682622307f
contract-base: 0c37e6d3902cf63c5baf2c81d2b54f8807897e24
clean-at-update: true
slice: Adds the first uniform admission-free case dispatcher. ConcreteStructuredCaseAltsNormalized records the minimal final-LCNF phase fact: zero or more constructor arms followed by at most one default. ConcreteStructuredCaseSafeAt contains only that normalized source syntax, the currently proved tobject/UInt8 discriminator representation, and the semantic wasm32 range law for object tags. Residual executable validation derives every constructor-tag bound, compiler-local equation, and discriminator mode. ConcreteStructuredValidatedCodeOutcome.advance_cases_of_source_safe_step then covers erased defaults, object-tag tests, and scalar-UInt8 tests behind one finite-path successor theorem, preserves the closed validated relation, and proves strict source-rank decrease whenever the target path is empty. The exact specialized costs remain available underneath: zero, five steps per object test, and four per UInt8 test.
files: integration/talos/FirTalos/ConcreteStructuredValidation.lean; coordination/lanes/wasm-proof.md
contracts: No shared source semantics, executable runtime behavior, compiler ABI, concrete memory layout, resident-helper signature, emitter, symbolic Wasm instruction, or W7 artifact changed. ConcreteStructuredCaseAltsNormalized, ConcreteStructuredCaseSafeAt, the validation-to-production bridge, and the uniform case successor are additive W6 proof-side interfaces. Existing specialized case theorems remain unchanged.
checks: Lean Beam update/sync/save reported zero errors for ConcreteStructuredValidation with only its two pre-existing warnings; targeted lake build FirTalos.ConcreteStructuredValidation passed all 3,127 jobs; the proof commit rebased cleanly onto main 0c37e6d3 as effb18a6; forced post-rebase Lean Beam refresh/save reported zero errors and the same two warnings; git diff --check and git diff main...HEAD --check passed; post-rebase make check passed with 719/719 source cases across native, LCNF, and V8, 9/9 direct-machine cases, 728 unique cases, 2,166/2,166 comparisons equal, zero findings, 209 active bug cards, and 31 mailbox tests; post-rebase make talos-check passed all 3,174 jobs.
bug-cards: FIR-BUG-impure-case-table-selector-determinism (existing; names the missing final-LCNF normalization phase bridge); FIR-BUG-wasm-none-return-admission-refinement-direction (existing; semantic transport and state-local return-safety boundaries solved; the global source-typing invariant/module dispatcher remains)
blockers: none
handoff: GREEN LIGHT. Resolve the containing status commit from wasm/talos-runtime and fast-forward functional head effb18a6, based directly at 0c37e6d3. The branch is rebased on current main and all required gates pass.
next: Prove structured finite-path execution for join introduction and jump transfer from the existing residual jump/join validation inversions; connect the already-proved let/call staging families behind the same uniform successor shape; assemble the module-wide validated one-step dispatcher; prove preservation of source semantic typing and finite address-space safety; then lift the dispatcher to ConcreteFiniteTraceCorrect.
```
